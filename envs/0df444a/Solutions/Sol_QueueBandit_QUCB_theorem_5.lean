-- Prove2me | solution 1 for QueueBandit.QUCB.theorem_5
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-04T01:44:11.537123+00:00
-- url     : https://prove2.me/submissions/d7a090bf-b1ef-464a-bb1c-aceda1df9250
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_QueueBandit_QUCB_Model
import Definitions.Def_QueueBandit_QUCB_Algorithm1
import Theorems.Thm_QueueBandit_QUCB_lemma_10_b
import Theorems.Thm_QueueBandit_QUCB_lemma_11
import Theorems.Thm_QueueBandit_QUCB_lemma_12
import Theorems.Thm_QueueBandit_QUCB_lemma_17

namespace QueueBandit.QUCB.T5aux

open MeasureTheory ProbabilityTheory QueueBandit.QUCB

variable {U K : ℕ}

theorem meas_dep {α β : Type*} [MeasurableSpace α] [Countable α] [MeasurableSingletonClass α]
    [MeasurableSpace β] {g : Ω U K → α} (hg : Measurable g) {F : α → Ω U K → β}
    (hF : ∀ a, Measurable (F a)) : Measurable fun ω => F (g ω) ω := by
  have h : Measurable fun p : Ω U K × α => F p.2 p.1 :=
    measurable_from_prod_countable_left (fun a => hF a)
  exact h.comp (measurable_id.prodMk hg)

theorem meas_seed (t : ℕ) : Measurable fun ω : Ω U K => ω.2 t :=
  (measurable_pi_apply t).comp measurable_snd

theorem meas_explore (t : ℕ) : Measurable (explore (U := U) (K := K) t) := by
  unfold explore
  refine Measurable.ite ?_ measurable_const measurable_const
  have : Measurable fun ω : Ω U K => (((ω.2 t).2.2.1 : unitInterval) : ℝ) :=
    measurable_subtype_coe.comp (measurable_fst.comp (measurable_snd.comp (measurable_snd.comp (meas_seed t))))
  exact measurableSet_lt this measurable_const

theorem meas_A (I : Instance U K) (u : Fin U) (t : ℕ) : Measurable (I.A u t) := by
  unfold Instance.A
  refine Measurable.ite ?_ measurable_const measurable_const
  have : Measurable fun ω : Ω U K => (((ω.2 t).1 u : unitInterval) : ℝ) :=
    measurable_subtype_coe.comp ((measurable_pi_apply u).comp (measurable_fst.comp (meas_seed t)))
  exact measurableSet_le this measurable_const

theorem meas_R (I : Instance U K) (u : Fin U) (k : Fin K) (t : ℕ) : Measurable (I.R u k t) := by
  unfold Instance.R
  refine Measurable.ite ?_ measurable_const measurable_const
  have : Measurable fun ω : Ω U K => (((ω.2 t).2.1 (u, k) : unitInterval) : ℝ) :=
    measurable_subtype_coe.comp ((measurable_pi_apply (u, k)).comp
      (measurable_fst.comp (measurable_snd.comp (meas_seed t))))
  exact measurableSet_le this measurable_const

theorem meas_step (A : QUCBRule U K) (I : Instance U K) (n : ℕ) (h : Hist U K n) :
    Measurable fun ω => A.step I n h ω := by
  have hκ : Measurable fun ω : Ω U K =>
      (if explore (n + 1) ω = 1 then A.X (ω.2 (n + 1)).2.2.2 else A.proj n h (A.sel n h)) := by
    refine Measurable.ite ?_ ?_ measurable_const
    · exact (meas_explore (n + 1)) (measurableSet_singleton 1)
    · exact (measurable_of_countable A.X).comp
        (measurable_snd.comp (measurable_snd.comp (measurable_snd.comp (meas_seed (n + 1)))))
  unfold QUCBRule.step
  refine hκ.prodMk ?_
  refine measurable_pi_lambda _ fun u => ?_
  exact meas_dep (F := fun (κ : Matching U K) ω => I.R u (κ.1 u) (n + 1) ω) hκ
    (fun κ => meas_R I u _ _)

theorem meas_hist (A : QUCBRule U K) (I : Instance U K) (n : ℕ) :
    Measurable (A.hist I n) := by
  induction n with
  | zero => exact measurable_const
  | succ n ih =>
    show Measurable fun ω => Fin.snoc (α := fun _ => Matching U K × (Fin U → ℕ)) (A.hist I n ω)
      (A.step I n (A.hist I n ω) ω)
    refine meas_dep (F := fun h ω => Fin.snoc (α := fun _ => Matching U K × (Fin U → ℕ)) h
      (A.step I n h ω)) ih (fun h => ?_)
    refine measurable_pi_lambda _ fun i => ?_
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa using meas_step A I n h
    · simpa using measurable_const

theorem meas_kappa (A : QUCBRule U K) (I : Instance U K) (t : ℕ) :
    Measurable (A.kappa I t) := by
  unfold QUCBRule.kappa
  exact measurable_fst.comp (meas_dep (F := fun h ω => A.step I (t - 1) h ω) (meas_hist A I _)
    (fun h => meas_step A I _ h))

theorem meas_S (A : QUCBRule U K) (I : Instance U K) (u : Fin U) (t : ℕ) :
    Measurable (A.S I u t) := by
  unfold QUCBRule.S
  exact meas_dep (F := fun (κ : Matching U K) ω => I.R u (κ.1 u) t ω) (meas_kappa A I t)
    (fun κ => meas_R I u _ _)

theorem meas_Q (A : QUCBRule U K) (I : Instance U K) (u : Fin U) (t : ℕ) :
    Measurable (A.Q I u t) := by
  induction t with
  | zero => exact (measurable_pi_apply u).comp measurable_fst
  | succ t ih =>
    show Measurable fun ω => A.Q I u t ω + I.A u (t + 1) ω - A.S I u (t + 1) ω
    exact (ih.add (meas_A I u _)).sub (meas_S A I u _)

theorem meas_Qstar (I : Instance U K) (u : Fin U) (t : ℕ) :
    Measurable (I.Qstar u t) := by
  induction t with
  | zero => exact (measurable_pi_apply u).comp measurable_fst
  | succ t ih =>
    show Measurable fun ω => I.Qstar u t ω + I.A u (t + 1) ω - I.R u (I.kstar u) (t + 1) ω
    exact (ih.add (meas_A I u _)).sub (meas_R I u _ _)

theorem meas_exploit (A : QUCBRule U K) (I : Instance U K) (u : Fin U) (k : Fin K) (t : ℕ) :
    Measurable (A.exploit I u k t) := by
  unfold QUCBRule.exploit
  refine Measurable.ite ?_ measurable_const measurable_const
  refine ((meas_explore t) (measurableSet_singleton 0)).inter ?_
  exact (meas_kappa A I t) (Set.Countable.measurableSet (Set.to_countable
    {κ : Matching U K | κ.1 u = k}))


theorem meas_B (A : QUCBRule U K) (I : Instance U K) (u : Fin U) (t : ℕ) :
    Measurable (A.B I u t) := by
  classical
  let vec : Ω U K → (Fin (t + 1) → ℕ) := fun ω i => A.Q I u i ω
  have hvec : Measurable vec := measurable_pi_lambda _ (fun i => meas_Q A I u i)
  let G : (Fin (t + 1) → ℕ) → ℕ := fun q =>
    if h : ∃ s, s ≤ t ∧ q (Fin.ofNat (t + 1) (t - s)) = 0 then Nat.find h else t
  have hG : A.B I u t = fun ω => G (vec ω) := by
    funext ω
    have hq : ∀ s, vec ω (Fin.ofNat (t + 1) (t - s)) = A.Q I u (t - s) ω := by
      intro s
      simp only [vec, Fin.val_ofNat]
      rw [Nat.mod_eq_of_lt (by omega)]
    simp only [G, hq]
    unfold QUCBRule.B
    rfl
  rw [hG]
  exact (measurable_of_countable G).comp hvec

theorem rho_nonneg (I : Instance U K) (u : Fin U) : 0 ≤ I.rho u := by
  have h1 := I.lam_nonneg u
  have h2 := I.lam_le_one u
  have h3 := I.mu_le_one u (I.kstar u)
  have h4 := I.stable u
  unfold Instance.rho Instance.muStar
  apply div_nonneg
  · exact mul_nonneg h1 (by linarith)
  · exact mul_nonneg (by linarith) (by linarith)

theorem rho_le_one (I : Instance U K) (u : Fin U) : I.rho u ≤ 1 := by
  have h1 := I.lam_nonneg u
  have h3 := I.mu_le_one u (I.kstar u)
  have h4 := I.stable u
  unfold Instance.rho Instance.muStar
  have hpos : 0 < (1 - I.lam u) * I.mu u (I.kstar u) := mul_pos (by linarith) (by linarith)
  rw [div_le_one hpos]
  nlinarith

theorem geom_partial (r : ℝ) (N : ℕ) :
    ∑ n ∈ Finset.range N, (1 - r) * r ^ n = 1 - r ^ N := by
  induction N with
  | zero => simp
  | succ N ih => rw [Finset.sum_range_succ, ih]; ring

theorem initLaw_univ_le (I : Instance U K) : I.initLaw Set.univ ≤ 1 := by
  classical
  rw [Instance.initLaw, Measure.sum_apply _ MeasurableSet.univ]
  simp only [Measure.smul_apply, measure_univ, smul_eq_mul, mul_one]
  rw [ENNReal.tsum_eq_iSup_sum]
  refine iSup_le fun F => ?_
  let N : ℕ := F.sup (fun q => Finset.univ.sup q) + 1
  have hsub : F ⊆ Fintype.piFinset (fun _ : Fin U => Finset.range N) := by
    intro q hq
    rw [Fintype.mem_piFinset]
    intro u
    rw [Finset.mem_range]
    have h1 : q u ≤ Finset.univ.sup q := Finset.le_sup (f := q) (Finset.mem_univ u)
    have h2 : Finset.univ.sup q ≤ F.sup (fun q => Finset.univ.sup q) :=
      Finset.le_sup (f := fun q => Finset.univ.sup q) hq
    omega
  have hnn : ∀ q : Fin U → ℕ, 0 ≤ ∏ u, (1 - I.rho u) * I.rho u ^ q u := by
    intro q
    exact Finset.prod_nonneg fun u _ =>
      mul_nonneg (by linarith [rho_le_one I u]) (pow_nonneg (rho_nonneg I u) _)
  calc ∑ q ∈ F, ENNReal.ofReal (∏ u, (1 - I.rho u) * I.rho u ^ q u)
      ≤ ∑ q ∈ Fintype.piFinset (fun _ : Fin U => Finset.range N),
          ENNReal.ofReal (∏ u, (1 - I.rho u) * I.rho u ^ q u) :=
        Finset.sum_le_sum_of_subset hsub
    _ = ENNReal.ofReal (∑ q ∈ Fintype.piFinset (fun _ : Fin U => Finset.range N),
          ∏ u, (1 - I.rho u) * I.rho u ^ q u) := by
        rw [ENNReal.ofReal_sum_of_nonneg (fun q _ => hnn q)]
    _ = ENNReal.ofReal (∏ u : Fin U, ∑ n ∈ Finset.range N, (1 - I.rho u) * I.rho u ^ n) := by
        rw [Finset.prod_univ_sum]
    _ ≤ ENNReal.ofReal 1 := by
        apply ENNReal.ofReal_le_ofReal
        apply Finset.prod_le_one
        · intro u _
          exact Finset.sum_nonneg fun n _ =>
            mul_nonneg (by linarith [rho_le_one I u]) (pow_nonneg (rho_nonneg I u) _)
        · intro u _
          rw [geom_partial]
          linarith [pow_nonneg (rho_nonneg I u) N]
    _ = 1 := ENNReal.ofReal_one

theorem uniformFin_univ (hK : 1 ≤ K) : uniformFin K Set.univ = 1 := by
  simp only [uniformFin, Measure.smul_apply, Measure.count_univ, smul_eq_mul]
  rw [ENat.card_eq_coe_fintype_card, Fintype.card_fin]
  simp only [ENat.toENNReal_coe]
  exact ENNReal.inv_mul_cancel (by exact_mod_cast (by omega : K ≠ 0)) (ENNReal.natCast_ne_top K)

instance uniformFin_prob (K : ℕ) [NeZero K] : IsProbabilityMeasure (uniformFin K) :=
  ⟨uniformFin_univ (Nat.one_le_iff_ne_zero.mpr (NeZero.ne K))⟩

instance seedLaw_prob [NeZero K] : IsProbabilityMeasure (seedLaw U K) := by
  unfold seedLaw; infer_instance

instance P_finite [NeZero K] (I : Instance U K) : IsFiniteMeasure I.P := by
  constructor
  rw [Instance.P, ← Set.univ_prod_univ, Measure.prod_prod]
  calc I.initLaw Set.univ * (Measure.infinitePi fun _ : ℕ => seedLaw U K) Set.univ
      ≤ 1 * 1 := by
        gcongr
        · exact initLaw_univ_le I
        · exact prob_le_one
    _ < ⊤ := by simp

theorem P_explore_le [NeZero K] (I : Instance U K) (l : ℕ) (p : ℝ) (hp : 0 ≤ p) :
    I.P {ω : Ω U K | (((ω.2 l).2.2.1 : unitInterval) : ℝ) < p} ≤ ENNReal.ofReal p := by
  let T' : Set (Seed U K) := Set.univ ×ˢ (Set.univ ×ˢ ({y : unitInterval | (y : ℝ) < p} ×ˢ Set.univ))
  have hy : MeasurableSet {y : unitInterval | (y : ℝ) < p} :=
    measurableSet_lt measurable_subtype_coe measurable_const
  have hT' : MeasurableSet T' :=
    MeasurableSet.univ.prod (MeasurableSet.univ.prod (hy.prod MeasurableSet.univ))
  let T : Set (ℕ → Seed U K) := (fun x => x l) ⁻¹' T'
  have hT : MeasurableSet T := (measurable_pi_apply l) hT'
  have hset : {ω : Ω U K | (((ω.2 l).2.2.1 : unitInterval) : ℝ) < p} = Set.univ ×ˢ T := by
    ext ω; simp [T, T']
  rw [hset, Instance.P, Measure.prod_prod]
  have h1 : (Measure.infinitePi fun _ : ℕ => seedLaw U K) T = seedLaw U K T' := by
    rw [← Measure.map_apply (measurable_pi_apply l) hT', Measure.infinitePi_map_eval]
  rw [h1]
  have h2 : seedLaw U K T' ≤ ENNReal.ofReal p := by
    simp only [T', seedLaw, Measure.prod_prod, measure_univ, one_mul, uniformFin_univ
      (Nat.one_le_iff_ne_zero.mpr (NeZero.ne K)), mul_one]
    rw [unitInterval.volume_apply]
    calc volume (Subtype.val '' {y : unitInterval | (y : ℝ) < p}) ≤ volume (Set.Ico (0 : ℝ) p) := by
          apply measure_mono
          rintro _ ⟨y, hy, rfl⟩
          exact ⟨y.2.1, hy⟩
      _ = ENNReal.ofReal p := by simp
  calc I.initLaw Set.univ * seedLaw U K T' ≤ 1 * ENNReal.ofReal p := by
        gcongr
        exact initLaw_univ_le I
    _ = ENNReal.ofReal p := one_mul _

end QueueBandit.QUCB.T5aux

namespace QueueBandit.QUCB.T5aux

open MeasureTheory QueueBandit.QUCB

variable {U K : ℕ}

theorem Q_diff_le (A : QUCBRule U K) (I : Instance U K) (u : Fin U) (t : ℕ) (ω : Ω U K) :
    A.Q I u t ω ≤ I.Qstar u t ω + t ∧ I.Qstar u t ω ≤ A.Q I u t ω + t := by
  induction t with
  | zero => simp [QUCBRule.Q, Instance.Qstar]
  | succ t ih =>
    have hr : I.R u (I.kstar u) (t + 1) ω ≤ 1 := by unfold Instance.R; split_ifs <;> simp
    have hs : A.S I u (t + 1) ω ≤ 1 := by
      unfold QUCBRule.S Instance.R; split_ifs <;> simp
    show A.Q I u t ω + I.A u (t + 1) ω - A.S I u (t + 1) ω ≤
        I.Qstar u t ω + I.A u (t + 1) ω - I.R u (I.kstar u) (t + 1) ω + (t + 1) ∧
      I.Qstar u t ω + I.A u (t + 1) ω - I.R u (I.kstar u) (t + 1) ω ≤
        A.Q I u t ω + I.A u (t + 1) ω - A.S I u (t + 1) ω + (t + 1)
    omega

theorem explore_le_one (l : ℕ) (ω : Ω U K) : explore (U := U) (K := K) l ω ≤ 1 := by
  unfold explore; split_ifs <;> simp

theorem arith_final (T x : ℝ) (hT : 5800 ≤ T) (hx : 0 ≤ x) :
    T * (x / (6 * T ^ 3)) + 1 / T ^ 3 + T * (4 / T ^ 3 + 2 / T ^ 4) ≤ (24.004 + x) / (6 * T ^ 2) := by
  have hT0 : 0 < T := by linarith
  have e : T * (x / (6 * T ^ 3)) + 1 / T ^ 3 + T * (4 / T ^ 3 + 2 / T ^ 4)
      = (x * T + 24 * T + 18) / (6 * T ^ 3) := by
    field_simp; ring
  rw [e, div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [mul_nonneg (mul_nonneg (sq_nonneg T) hT0.le) hx,
    mul_nonneg (sq_nonneg T) (by linarith : (0 : ℝ) ≤ 0.004 * T - 18)]

theorem hw10_of (L a g : ℝ) (hL : 0 < L) (ha : 0 < a) (hg : 0 < g) (hg1 : g ≤ 1)
    (h : 4 / (g ^ 2 * a ^ 3) ≤ L) : (2 * L) ^ ((2 : ℝ) / 3) ≤ a * L := by
  have h1 : 4 / a ^ 3 ≤ 4 / (g ^ 2 * a ^ 3) := by
    apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
    have : g ^ 2 ≤ 1 := by nlinarith
    nlinarith [pow_pos ha 3]
  have h2 : 4 ≤ a ^ 3 * L := by
    have := h1.trans h
    rwa [div_le_iff₀ (by positivity), mul_comm] at this
  apply le_of_pow_le_pow_left₀ (n := 3) (by norm_num) (by positivity)
  have e : ((2 * L) ^ ((2 : ℝ) / 3)) ^ 3 = (2 * L) ^ 2 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
    norm_num
  rw [e]
  nlinarith [sq_nonneg L, mul_le_mul_of_nonneg_right h2 (sq_nonneg L)]

theorem meas_cast {f : Ω U K → ℕ} (hf : Measurable f) : Measurable fun ω => (f ω : ℝ) :=
  (measurable_of_countable (fun n : ℕ => (n : ℝ))).comp hf

end QueueBandit.QUCB.T5aux

open MeasureTheory QueueBandit.QUCB QueueBandit.QUCB.T5aux in
theorem solution {U K : ℕ} (hUK : U ≤ K) (hK : 2 ≤ K) (I : Instance U K)
    (A : QUCBRule U K) (β : ℝ) (hβ : 1 < β) (u : Fin U) (t : ℕ) (ht : 5800 ≤ t)
    (hΔ : Real.exp (4 / (I.gap ^ 2 * (1 - 1 / β) ^ 3)) ≤ t)
    (hw : 2 / I.eps u ≤ w β t / Real.log t) (hv : I.v β u t + I.vPrime β u t ≤ (t : ℝ) / 2) :
    MeasureTheory.Integrable (fun ω => (A.Q I u t ω : ℝ) - (I.Qstar u t ω : ℝ)) I.P ∧
      A.Psi I u t ≤
        6 * K * (I.v β u t * Real.log t ^ 2) / t + (24.004 + U * K) / (6 * (t : ℝ) ^ 2) := by
  classical
  haveI : NeZero K := ⟨by omega⟩
  -- basic facts
  have htpos : (0 : ℝ) < t := by exact_mod_cast (by omega : 0 < t)
  have ht5800 : (5800 : ℝ) ≤ t := by exact_mod_cast ht
  have hlogt : 0 < Real.log t := Real.log_pos (by linarith)
  have heps : 0 < I.eps u := by
    unfold Instance.eps Instance.muStar; linarith [I.stable u]
  have heps1 : I.eps u ≤ 1 := by
    unfold Instance.eps Instance.muStar; linarith [I.mu_le_one u (I.kstar u), I.lam_nonneg u]
  have hKr : (2 : ℝ) ≤ K := by exact_mod_cast hK
  have hwnn : 0 ≤ w β t := Real.rpow_nonneg htpos.le _
  have hvP : w β t ≤ I.vPrime β u t := by
    unfold Instance.vPrime
    have : (1 : ℝ) ≤ 6 * K / I.eps u := by
      rw [le_div_iff₀ heps]; nlinarith
    nlinarith
  have hvPnn : 0 ≤ I.vPrime β u t := le_trans hwnn hvP
  have hvnn : 0 ≤ I.v β u t := by
    unfold Instance.v
    have h1 : 0 ≤ 24 / I.eps u ^ 2 * Real.log t := by positivity
    have h2 : 0 ≤ 60 * K / I.eps u * (I.vPrime β u t * Real.log t ^ 2 / t) := by positivity
    linarith
  -- the difference
  set D : Ω U K → ℝ := fun ω => (A.Q I u t ω : ℝ) - (I.Qstar u t ω : ℝ) with hD
  have hDmeas : Measurable D := (meas_cast (meas_Q A I u t)).sub (meas_cast (meas_Qstar I u t))
  have hDbound : ∀ ω, |D ω| ≤ t := by
    intro ω
    obtain ⟨h1, h2⟩ := Q_diff_le A I u t ω
    have h1' : (A.Q I u t ω : ℝ) ≤ I.Qstar u t ω + t := by exact_mod_cast h1
    have h2' : (I.Qstar u t ω : ℝ) ≤ A.Q I u t ω + t := by exact_mod_cast h2
    rw [abs_le]; constructor <;> simp only [hD] <;> linarith
  have hDint : Integrable D I.P :=
    Integrable.of_bound hDmeas.aestronglyMeasurable (t : ℝ)
      (Filter.Eventually.of_forall fun ω => by
        rw [Real.norm_eq_abs]; exact hDbound ω)
  refine ⟨hDint, ?_⟩
  -- hypothesis for Lemma 10(b)
  have hU : 0 < U := Fin.pos u
  have hne : I.subPairs.Nonempty := by
    let k' : Fin K := if (I.kstar u).val = 0 then ⟨1, by omega⟩ else ⟨0, by omega⟩
    have hk' : k' ≠ I.kstar u := by
      intro h
      have hv' := congrArg Fin.val h
      by_cases h0 : (I.kstar u).val = 0
      · simp [k', h0] at hv' <;> omega
      · simp [k', h0] at hv' <;> omega
    exact ⟨(u, k'), by simp [Instance.subPairs, hk']⟩
  have hgpos : 0 < I.gap := by
    unfold Instance.gap
    rw [dif_pos hne, Finset.lt_inf'_iff]
    intro p hp
    simp only [Instance.subPairs, Finset.mem_filter, Finset.mem_univ, true_and] at hp
    have := I.kstar_unique p.1 p.2 hp
    unfold Instance.muStar; linarith
  have hg1 : I.gap ≤ 1 := by
    unfold Instance.gap
    rw [dif_pos hne]
    obtain ⟨p, hp⟩ := hne
    refine (Finset.inf'_le _ hp).trans ?_
    unfold Instance.muStar
    linarith [I.mu_le_one p.1 (I.kstar p.1), I.mu_nonneg p.1 p.2]
  have ha : 0 < 1 - 1 / β := by
    have : 1 / β < 1 := by rw [div_lt_one (by linarith)]; exact hβ
    linarith
  have hlogΔ : 4 / (I.gap ^ 2 * (1 - 1 / β) ^ 3) ≤ Real.log t :=
    (Real.le_log_iff_exp_le htpos).mpr hΔ
  have hw10 : (2 * Real.log t) ^ ((2 : ℝ) / 3) ≤ Real.log (w β t) := by
    rw [w, Real.log_rpow htpos]
    exact hw10_of _ _ _ hlogt ha hgpos hg1 hlogΔ
  -- events
  set v := I.v β u t with hvdef
  set m := ⌊v⌋₊ with hmdef
  set E1s := A.E1 I β t with hE1s
  set E2s := (E2 (U := U) (K := K) β t) with hE2s
  set Ss := {ω | v < (A.B I u t ω : ℝ)} ∩ E1s ∩ E2s with hSs
  have hE1m : MeasurableSet E1s := by
    have hg : Measurable fun ω => ∑ l ∈ Finset.Ioc ⌊w β t⌋₊ t, ∑ u, ∑ k ∈ Finset.univ.filter
        (fun k => k ≠ I.kstar u), A.exploit I u k l ω :=
      Finset.measurable_sum _ fun l _ => Finset.measurable_sum _ fun u _ =>
        Finset.measurable_sum _ fun k _ => meas_exploit A I u k l
    exact hg (measurableSet_singleton 0)
  have hE2m : MeasurableSet E2s := by
    have hg : Measurable fun ω : Ω U K => ((∑ l ∈ Finset.Icc 1 t, explore l ω : ℕ) : ℝ) :=
      meas_cast (Finset.measurable_sum _ fun l _ => meas_explore l)
    exact measurableSet_le hg measurable_const
  have hSm : MeasurableSet Ss :=
    ((measurableSet_lt measurable_const (meas_cast (meas_B A I u t))).inter hE1m).inter hE2m
  have hmv : (m : ℝ) ≤ v := Nat.floor_le hvnn
  have hmt : m ≤ t := by
    have : (m : ℝ) ≤ t := by linarith
    exact_mod_cast this
  -- pointwise bound
  set f : Ω U K → ℝ := fun ω => (∑ l ∈ Finset.Ioc (t - m) t, (explore l ω : ℝ)) +
      t * E1sᶜ.indicator 1 ω + t * E2sᶜ.indicator 1 ω + t * Ss.indicator 1 ω with hf
  have hsumE_nn : ∀ ω : Ω U K, 0 ≤ ∑ l ∈ Finset.Ioc (t - m) t, (explore l ω : ℝ) :=
    fun ω => Finset.sum_nonneg fun l _ => Nat.cast_nonneg _
  have hind_nn : ∀ (S : Set (Ω U K)) (ω : Ω U K), 0 ≤ (t : ℝ) * S.indicator 1 ω := fun S ω =>
    mul_nonneg htpos.le (Set.indicator_nonneg (fun _ _ => zero_le_one) ω)
  have hpt : ∀ ω, D ω ≤ f ω := by
    intro ω
    have h12 := QueueBandit.QUCB.lemma_12 hUK hK I A u t (by omega) ω
    have h12r : D ω ≤ ∑ l ∈ Finset.Ioc (t - A.B I u t ω) t, ((explore l ω : ℝ) +
        ∑ k ∈ Finset.univ.filter (fun k => k ≠ I.kstar u), (A.exploit I u k l ω : ℝ)) := by
      have := (Int.cast_le (R := ℝ)).mpr h12
      push_cast at this
      exact this
    by_cases hg : ω ∈ E1s ∧ ω ∈ E2s ∧ (A.B I u t ω : ℝ) ≤ v
    · obtain ⟨hg1, hg2, hg3⟩ := hg
      have hBm : A.B I u t ω ≤ m := Nat.le_floor hg3
      have hBt : A.B I u t ω ≤ t := by omega
      have hwB : ⌊w β t⌋₊ ≤ t - A.B I u t ω := by
        have h1 : (⌊w β t⌋₊ : ℝ) ≤ w β t := Nat.floor_le hwnn
        have h2 : (((t - A.B I u t ω : ℕ)) : ℝ) = t - A.B I u t ω := by
          rw [Nat.cast_sub hBt]
        have : (⌊w β t⌋₊ : ℝ) ≤ ((t - A.B I u t ω : ℕ) : ℝ) := by
          rw [h2]; linarith
        exact_mod_cast this
      have hzero : ∀ l ∈ Finset.Ioc (t - A.B I u t ω) t,
          ∑ k ∈ Finset.univ.filter (fun k => k ≠ I.kstar u), (A.exploit I u k l ω : ℝ) = 0 := by
        intro l hl
        have hl' : l ∈ Finset.Ioc ⌊w β t⌋₊ t := by
          simp only [Finset.mem_Ioc] at hl ⊢; omega
        have hE := hg1
        simp only [hE1s, QUCBRule.E1, Set.mem_setOf_eq] at hE
        have h1 := (Finset.sum_eq_zero_iff.mp hE) l hl'
        have h2 := (Finset.sum_eq_zero_iff.mp h1) u (Finset.mem_univ u)
        exact_mod_cast h2
      calc D ω ≤ _ := h12r
        _ = ∑ l ∈ Finset.Ioc (t - A.B I u t ω) t, (explore l ω : ℝ) := by
          apply Finset.sum_congr rfl
          intro l hl
          rw [hzero l hl, add_zero]
        _ ≤ ∑ l ∈ Finset.Ioc (t - m) t, (explore l ω : ℝ) := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · exact Finset.Ioc_subset_Ioc (by omega) le_rfl
          · intro _ _ _; exact Nat.cast_nonneg _
        _ ≤ f ω := by
          simp only [hf]
          linarith [hind_nn E1sᶜ ω, hind_nn E2sᶜ ω, hind_nn Ss ω]
    · have hDt : D ω ≤ t := (le_abs_self _).trans (hDbound ω)
      have hone : (t : ℝ) ≤ t * E1sᶜ.indicator 1 ω + t * E2sᶜ.indicator 1 ω +
          t * Ss.indicator 1 ω := by
        by_cases h1 : ω ∈ E1s
        · by_cases h2 : ω ∈ E2s
          · have h3 : ω ∈ Ss := by
              refine ⟨⟨?_, h1⟩, h2⟩
              show v < (A.B I u t ω : ℝ)
              by_contra h3
              exact hg ⟨h1, h2, not_lt.mp h3⟩
            rw [Set.indicator_of_mem h3]
            simp only [Pi.one_apply, mul_one]
            linarith [hind_nn E1sᶜ ω, hind_nn E2sᶜ ω]
          · rw [Set.indicator_of_mem (show ω ∈ E2sᶜ from h2)]
            simp only [Pi.one_apply, mul_one]
            linarith [hind_nn E1sᶜ ω, hind_nn Ss ω]
        · rw [Set.indicator_of_mem (show ω ∈ E1sᶜ from h1)]
          simp only [Pi.one_apply, mul_one]
          linarith [hind_nn E2sᶜ ω, hind_nn Ss ω]
      simp only [hf]
      linarith [hsumE_nn ω]
  -- integrability
  have hEint : ∀ l, Integrable (fun ω : Ω U K => (explore l ω : ℝ)) I.P := fun l =>
    Integrable.of_bound (meas_cast (meas_explore l)).aestronglyMeasurable 1
      (Filter.Eventually.of_forall fun ω => by
        rw [Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg _)]
        exact_mod_cast explore_le_one l ω)
  have hIint : ∀ S : Set (Ω U K), MeasurableSet S →
      Integrable (fun ω => (t : ℝ) * S.indicator 1 ω) I.P := fun S hS =>
    ((integrable_const (1 : ℝ)).indicator hS).const_mul _
  have hf1int : Integrable (fun ω => ∑ l ∈ Finset.Ioc (t - m) t, (explore l ω : ℝ)) I.P :=
    integrable_finset_sum _ fun l _ => hEint l
  have hfint : Integrable f I.P :=
    ((hf1int.add (hIint _ hE1m.compl)).add (hIint _ hE2m.compl)).add (hIint _ hSm)
  have hIval : ∀ S : Set (Ω U K), MeasurableSet S →
      ∫ ω, (t : ℝ) * S.indicator 1 ω ∂I.P = t * I.P.real S := fun S hS => by
    rw [integral_const_mul, integral_indicator_one hS]
  have hintf : ∫ ω, f ω ∂I.P = (∑ l ∈ Finset.Ioc (t - m) t, ∫ ω, (explore l ω : ℝ) ∂I.P) +
      t * I.P.real E1sᶜ + t * I.P.real E2sᶜ + t * I.P.real Ss := by
    simp only [hf]
    rw [integral_add, integral_add, integral_add, integral_finset_sum _ fun l _ => hEint l,
      hIval _ hE1m.compl, hIval _ hE2m.compl, hIval _ hSm]
    · exact hf1int
    · exact hIint _ hE1m.compl
    · exact hf1int.add (hIint _ hE1m.compl)
    · exact hIint _ hE2m.compl
    · exact (hf1int.add (hIint _ hE1m.compl)).add (hIint _ hE2m.compl)
    · exact hIint _ hSm
  -- bound on the explore expectations
  have hEl : ∀ l ∈ Finset.Ioc (t - m) t,
      ∫ ω, (explore l ω : ℝ) ∂I.P ≤ 6 * K * Real.log t ^ 2 / t := by
    intro l hl
    simp only [Finset.mem_Ioc] at hl
    set p := exploreProb K l with hp
    have hl1 : (1 : ℝ) ≤ l := by exact_mod_cast (by omega : 1 ≤ l)
    have hlpos : (0 : ℝ) < l := by linarith
    have hpnn : 0 ≤ p := le_min zero_le_one (by positivity)
    have hset : (fun ω : Ω U K => (explore l ω : ℝ)) =
        {ω : Ω U K | (((ω.2 l).2.2.1 : unitInterval) : ℝ) < p}.indicator 1 := by
      funext ω
      unfold explore
      by_cases h : (((ω.2 l).2.2.1 : unitInterval) : ℝ) < exploreProb K l
      · rw [if_pos h, Set.indicator_of_mem (show ω ∈ _ from h)]; simp
      · rw [if_neg h, Set.indicator_of_notMem (show ω ∉ _ from h)]; simp
    have hms : MeasurableSet {ω : Ω U K | (((ω.2 l).2.2.1 : unitInterval) : ℝ) < p} :=
      measurableSet_lt (measurable_subtype_coe.comp (measurable_fst.comp (measurable_snd.comp
        (measurable_snd.comp (meas_seed l))))) measurable_const
    rw [hset, integral_indicator_one hms, measureReal_def]
    have h1 : (I.P {ω : Ω U K | (((ω.2 l).2.2.1 : unitInterval) : ℝ) < p}).toReal ≤ p :=
      ENNReal.toReal_le_of_le_ofReal hpnn (P_explore_le I l p hpnn)
    refine h1.trans ?_
    have h2 : p ≤ 3 * K * Real.log l ^ 2 / l := min_le_right _ _
    refine h2.trans ?_
    have hlt2 : (t : ℝ) ≤ 2 * l := by
      have : t < l + m := by omega
      have : (t : ℝ) < l + m := by exact_mod_cast this
      linarith
    have hlog : Real.log l ≤ Real.log t :=
      Real.log_le_log hlpos (by exact_mod_cast hl.2)
    have hlog0 : 0 ≤ Real.log l := Real.log_nonneg hl1
    have hsq : Real.log l ^ 2 ≤ Real.log t ^ 2 := by nlinarith
    rw [div_le_div_iff₀ hlpos htpos]
    have hK0 : (0 : ℝ) ≤ K := by linarith
    nlinarith [mul_le_mul_of_nonneg_left hsq (mul_nonneg hK0 htpos.le),
      mul_le_mul_of_nonneg_left hlt2 (mul_nonneg hK0 (sq_nonneg (Real.log t)))]
  have hsumE : (∑ l ∈ Finset.Ioc (t - m) t, ∫ ω, (explore l ω : ℝ) ∂I.P) ≤
      6 * K * (v * Real.log t ^ 2) / t := by
    refine (Finset.sum_le_sum hEl).trans ?_
    rw [Finset.sum_const, Nat.card_Ioc, nsmul_eq_mul, show t - (t - m) = m by omega]
    have hc : 0 ≤ 6 * K * Real.log t ^ 2 / t := by positivity
    calc (m : ℝ) * (6 * K * Real.log t ^ 2 / t) ≤ v * (6 * K * Real.log t ^ 2 / t) :=
          mul_le_mul_of_nonneg_right hmv hc
      _ = 6 * K * (v * Real.log t ^ 2) / t := by ring
  -- probability bounds
  have hP1 : I.P.real E1sᶜ ≤ (U : ℝ) * K / (6 * (t : ℝ) ^ 3) :=
    QueueBandit.QUCB.lemma_11 hUK hK I A β hβ t ht hΔ
  have hP2 : I.P.real E2sᶜ ≤ ((t : ℝ) ^ (2 * K))⁻¹ := by
    have hc : E2sᶜ = {ω : Ω U K | (K : ℝ) * w β t <
        ((∑ l ∈ Finset.Icc 1 t, explore l ω : ℕ) : ℝ)} := by
      ext ω; simp [hE2s, E2, not_le]
    rw [hc]
    exact QueueBandit.QUCB.lemma_10_b hUK hK I β hβ t ht hw10
  have hP3 : I.P.real Ss ≤ 4 / (t : ℝ) ^ 3 + 2 / (t : ℝ) ^ 4 :=
    QueueBandit.QUCB.lemma_17 hUK hK I A β hβ u t hw hv
  have hpow : ((t : ℝ) ^ (2 * K))⁻¹ ≤ ((t : ℝ) ^ 4)⁻¹ := by
    apply inv_anti₀ (by positivity)
    exact pow_le_pow_right₀ (by linarith) (by omega)
  have hfin := arith_final (t : ℝ) ((U : ℝ) * K) ht5800 (by positivity)
  have hPsi : A.Psi I u t = ∫ ω, D ω ∂I.P := rfl
  rw [hPsi]
  calc ∫ ω, D ω ∂I.P ≤ ∫ ω, f ω ∂I.P := integral_mono hDint hfint hpt
    _ = _ := hintf
    _ ≤ 6 * K * (v * Real.log t ^ 2) / t + t * ((U : ℝ) * K / (6 * (t : ℝ) ^ 3)) +
        t * ((t : ℝ) ^ 4)⁻¹ + t * (4 / (t : ℝ) ^ 3 + 2 / (t : ℝ) ^ 4) := by
      gcongr
      exact hP2.trans hpow
    _ ≤ 6 * K * (v * Real.log t ^ 2) / t + (24.004 + U * K) / (6 * (t : ℝ) ^ 2) := by
      have e : (t : ℝ) * ((t : ℝ) ^ 4)⁻¹ = 1 / (t : ℝ) ^ 3 := by
        field_simp
      rw [e]
      linarith
