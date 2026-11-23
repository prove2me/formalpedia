-- Prove2me | solution 1 for PhysReaudit.proposition_3_lower
-- status  : ACCEPTED   (prove)
-- author  : @jdenwood
-- created : 2026-11-23T14:01:49.640025+00:00
-- url     : https://prove2.me/submissions/08ab54d0-b463-48ae-a00a-2b4ad06b63b7

import Mathlib
import Definitions.Def_LimitedPriceChanges_LowerBound_KL
import Definitions.Def_PhysReaudit_mu
import Definitions.Def_PhysReaudit_Delta
import Definitions.Def_PhysReaudit_Rule
import Definitions.Def_PhysReaudit_run
import Definitions.Def_PhysReaudit_lawQ

open MeasureTheory

namespace PR3L
open PhysReaudit

/-! ### Countability / measurable structure on configurations -/

instance instCountableAction : Countable Action := by
  have : Function.Injective (fun o : Action => match o with
    | .setup => (0 : ℕ) | .attempt => 1 | .accept => 2 | .stop => 3) := by
    intro o1 o2 h; cases o1 <;> cases o2 <;> simp_all
  exact this.countable

instance instMSCAction : MeasurableSingletonClass Action := ⟨fun _ => trivial⟩

instance instCountableObs : Countable Obs := by
  have : Function.Injective (fun o : Obs => match o with
    | .started => (false, false, false) | .nav b => (true, false, b)
    | .target b => (true, true, b)) := by
    intro o1 o2 h; cases o1 <;> cases o2 <;> simp_all
  exact this.countable

instance instCountableCfg : Countable Cfg := by
  have : Function.Injective (fun c : Cfg => (c.hist, c.pos, c.navUsed, c.tgtUsed, c.halted)) := by
    intro c1 c2 h; cases c1; cases c2; simp_all
  exact this.countable

instance instMSCfg : MeasurableSpace Cfg := ⊤

instance instMSCCfg : MeasurableSingletonClass Cfg := ⟨fun _ => trivial⟩

/-! ### Step lemmas -/

lemma step_local (d : ℕ) (x y : ℕ → Bool) (act : Action) (c : Cfg) :
    step d x y act c = step d (fun _ => x c.navUsed) (fun _ => y c.tgtUsed) act c := rfl

lemma step_navUsed_mono (d : ℕ) (x y : ℕ → Bool) (act : Action) (c : Cfg) :
    c.navUsed ≤ (step d x y act c).navUsed := by
  rcases c with ⟨hs, p, nu, tu, hl⟩
  rcases hl with _ | b
  · cases act
    · simp [step]
    · rcases p with _ | i
      · simp [step]
      · by_cases hi : i < d <;> simp [step, hi]
    · simp [step]
    · simp [step]
  · simp [step]

lemma step_tgt_mono (d : ℕ) (x y : ℕ → Bool) (act : Action) (c : Cfg) :
    c.tgtUsed ≤ (step d x y act c).tgtUsed := by
  rcases c with ⟨hs, p, nu, tu, hl⟩
  rcases hl with _ | b
  · cases act
    · simp [step]
    · rcases p with _ | i
      · simp [step]
      · by_cases hi : i < d <;> simp [step, hi]
    · simp [step]
    · simp [step]
  · simp [step]

lemma step_len_le (d : ℕ) (x y : ℕ → Bool) (act : Action) (c : Cfg) :
    (step d x y act c).hist.length ≤ c.hist.length + 1 := by
  rcases c with ⟨hs, p, nu, tu, hl⟩
  rcases hl with _ | b
  · cases act
    · simp [step]
    · rcases p with _ | i
      · simp [step]
      · by_cases hi : i < d <;> simp [step, hi]
    · simp [step]
    · simp [step]
  · simp [step]

lemma step_noread (d : ℕ) (x x' y : ℕ → Bool) (act : Action) (c : Cfg)
    (h : (step d x y act c).navUsed = c.navUsed) : step d x' y act c = step d x y act c := by
  rcases c with ⟨hs, p, nu, tu, hl⟩
  rcases hl with _ | b
  · cases act
    · simp [step]
    · rcases p with _ | i
      · simp [step]
      · by_cases hi : i < d
        · simp [step, hi] at h
        · simp [step, hi]
    · simp [step]
    · simp [step]
  · simp [step]

/-! ### Run lemmas -/

lemma run_succ {W : Type} [MeasurableSpace W] (R : Rule W) (d : ℕ) (ω : Omega W) (n : ℕ) :
    run R d ω (n + 1) = step d ω.2.1 ω.2.2 (R.decide ω.1 (run R d ω n).hist) (run R d ω n) := rfl

lemma run_len_le {W : Type} [MeasurableSpace W] (R : Rule W) (d : ℕ) (ω : Omega W) (n : ℕ) :
    (run R d ω n).hist.length ≤ n := by
  induction n with
  | zero => simp [run, Cfg.init]
  | succ n ih => rw [run_succ]; exact (step_len_le _ _ _ _ _).trans (by omega)

lemma run_update {W : Type} [MeasurableSpace W] (R : Rule W) (d : ℕ) (w : W) (x y : ℕ → Bool)
    (k : ℕ) (b : Bool) : ∀ n, (run R d (w, (x, y)) n).navUsed ≤ k →
    run R d (w, (Function.update x k b, y)) n = run R d (w, (x, y)) n := by
  intro n
  induction n with
  | zero => intro _; rfl
  | succ n ih =>
    intro hk
    have hmono := step_navUsed_mono d x y (R.decide w (run R d (w, (x, y)) n).hist)
      (run R d (w, (x, y)) n)
    have hk' : (step d x y (R.decide w (run R d (w, (x, y)) n).hist)
      (run R d (w, (x, y)) n)).navUsed ≤ k := hk
    rw [run_succ, run_succ, ih (hmono.trans hk')]
    simp only
    set c := run R d (w, (x, y)) n
    rcases Nat.lt_or_ge c.navUsed k with hlt | hge
    · rw [step_local, step_local d x]
      rw [Function.update_of_ne (Nat.ne_of_lt hlt)]
    · exact step_noread _ _ _ _ _ _ (le_antisymm (hk'.trans hge) hmono)

/-! ### Measurability -/

lemma measurable_run {W : Type} [MeasurableSpace W] (R : Rule W) (d : ℕ) (n : ℕ) :
    Measurable (fun ω : Omega W => run R d ω n) := by
  induction n with
  | zero => exact measurable_const
  | succ n ih =>
    have key : ∀ c0 : Cfg, Measurable
        (fun ω : Omega W => step d ω.2.1 ω.2.2 (R.decide ω.1 c0.hist) c0) := by
      intro c0
      have h1 : Measurable (fun ω : Omega W =>
          (R.decide ω.1 c0.hist, ω.2.1 c0.navUsed, ω.2.2 c0.tgtUsed)) :=
        ((R.measurable_decide _).comp measurable_fst).prodMk
          (((measurable_pi_apply _).comp (measurable_fst.comp measurable_snd)).prodMk
            ((measurable_pi_apply _).comp (measurable_snd.comp measurable_snd)))
      exact (measurable_of_countable
        (fun p : Action × Bool × Bool => step d (fun _ => p.2.1) (fun _ => p.2.2) p.1 c0)).comp h1
    have hf : Measurable (fun p : Omega W × Cfg =>
        step d p.1.2.1 p.1.2.2 (R.decide p.1.1 p.2.hist) p.2) :=
      measurable_from_prod_countable_left (fun c0 => key c0)
    exact hf.comp (measurable_id.prodMk ih)

lemma measurable_run_decide {W : Type} [MeasurableSpace W] (R : Rule W) (d : ℕ) (n : ℕ) :
    Measurable (fun ω : Omega W => (run R d ω n, R.decide ω.1 (run R d ω n).hist)) := by
  have hf : Measurable (fun p : Omega W × Cfg => (p.2, R.decide p.1.1 p.2.hist)) :=
    measurable_from_prod_countable_left (fun c0 =>
      measurable_const.prodMk (by exact (R.measurable_decide c0.hist).comp measurable_fst))
  exact hf.comp (measurable_id.prodMk (measurable_run R d n))

/-! ### Bernoulli and tape independence -/

lemma bern_prob {r : ℝ} (h0 : 0 ≤ r) (h1 : r ≤ 1) : IsProbabilityMeasure (bern r) := by
  constructor
  simp only [bern, Measure.coe_add, Measure.coe_smul, Pi.add_apply, Pi.smul_apply, measure_univ,
    smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_add h0 (by linarith)]; simp

lemma bern_true (r : ℝ) : bern r {true} = ENNReal.ofReal r := by simp [bern]

lemma map_update_eq (μ0 : Measure Bool) [IsProbabilityMeasure μ0] (k : ℕ) :
    ((Measure.infinitePi fun _ : ℕ => μ0).prod μ0).map
      (fun p : (ℕ → Bool) × Bool => Function.update p.1 k p.2)
      = Measure.infinitePi fun _ : ℕ => μ0 := by
  apply Measure.eq_infinitePi
  intro s t ht
  classical
  rw [Measure.map_apply measurable_update' (MeasurableSet.pi s.countable_toSet (fun i _ => ht i))]
  by_cases hk : k ∈ s
  · have : (fun p : (ℕ → Bool) × Bool => Function.update p.1 k p.2) ⁻¹' Set.pi s t
        = Set.pi (s.erase k : Set ℕ) t ×ˢ t k := by
      ext ⟨x, b⟩
      simp only [Set.mem_preimage, Set.mem_pi, Finset.mem_coe, Set.mem_prod, Finset.mem_erase]
      constructor
      · intro h
        refine ⟨fun i ⟨hik, his⟩ => ?_, ?_⟩
        · have := h i his; rwa [Function.update_of_ne hik] at this
        · have := h k hk; rwa [Function.update_self] at this
      · rintro ⟨h1, h2⟩ i his
        by_cases hik : i = k
        · subst hik; rwa [Function.update_self]
        · rw [Function.update_of_ne hik]; exact h1 i ⟨hik, his⟩
    rw [this, Measure.prod_prod, Measure.infinitePi_pi _ (fun i _ => ht i),
      Finset.prod_erase_mul _ _ hk]
  · have : (fun p : (ℕ → Bool) × Bool => Function.update p.1 k p.2) ⁻¹' Set.pi s t
        = Set.pi (s : Set ℕ) t ×ˢ Set.univ := by
      ext ⟨x, b⟩
      simp only [Set.mem_preimage, Set.mem_pi, Finset.mem_coe, Set.mem_prod, Set.mem_univ,
        and_true]
      refine forall₂_congr fun i his => ?_
      have hik : i ≠ k := fun h => hk (h ▸ his)
      rw [Function.update_of_ne hik]
    rw [this, Measure.prod_prod, Measure.infinitePi_pi _ (fun i _ => ht i), measure_univ, mul_one]

lemma tape_indep {r : ℝ} (h0 : 0 ≤ r) (h1 : r ≤ 1) (k : ℕ) {A : Set (ℕ → Bool)}
    (hA : MeasurableSet A) (hinv : ∀ x b, Function.update x k b ∈ A ↔ x ∈ A) :
    (Measure.infinitePi fun _ : ℕ => bern r) (A ∩ {x | x k = true})
      = ENNReal.ofReal r * (Measure.infinitePi fun _ : ℕ => bern r) A := by
  have := bern_prob h0 h1
  have hm : MeasurableSet (A ∩ {x : ℕ → Bool | x k = true}) :=
    hA.inter (measurableSet_eq_fun (measurable_pi_apply k) measurable_const)
  conv_lhs => rw [← map_update_eq (bern r) k]
  rw [Measure.map_apply measurable_update' hm]
  have : (fun p : (ℕ → Bool) × Bool => Function.update p.1 k p.2) ⁻¹' (A ∩ {x | x k = true})
      = A ×ˢ {true} := by
    ext ⟨x, b⟩; simp [hinv]
  rw [this, Measure.prod_prod, bern_true, mul_comm]

lemma lawQ_indep {W : Type} [MeasurableSpace W] (ν : Measure W) [IsProbabilityMeasure ν]
    {a q : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (k : ℕ)
    {E : Set (Omega W)} (hE : MeasurableSet E)
    (hinv : ∀ w x y b, ((w, (Function.update x k b, y)) : Omega W) ∈ E ↔ (w, (x, y)) ∈ E) :
    lawQ ν a q (E ∩ {ω | ω.2.1 k = true}) = ENNReal.ofReal a * lawQ ν a q E := by
  have := bern_prob ha0 ha1
  have := bern_prob hq0 hq1
  have hm : MeasurableSet (E ∩ {ω : Omega W | ω.2.1 k = true}) :=
    hE.inter (measurableSet_eq_fun ((measurable_pi_apply k).comp (measurable_fst.comp
      measurable_snd)) measurable_const)
  simp only [lawQ]
  rw [Measure.prod_apply hm, Measure.prod_apply hE,
    ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_congr fun w => ?_
  rw [Measure.prod_apply_symm (measurable_prodMk_left hm),
    Measure.prod_apply_symm (measurable_prodMk_left hE),
    ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_congr fun y => ?_
  have := tape_indep ha0 ha1 k (A := {x | ((w, (x, y)) : Omega W) ∈ E})
    (measurable_prodMk_right (measurable_prodMk_left hE)) (fun x b => hinv w x y b)
  convert this using 2 <;> rfl

/-! ### The potential -/

/-- The (nonnegative) potential `χ = −ψ`. -/
noncomputable def chi (a : ℝ) (d : ℕ) : Option ℕ → ℝ
  | none => 0
  | some i => a ^ (d - i) * mu a d - ∑ j ∈ Finset.range (d - i + 1), a ^ j

@[simp] lemma chi_none (a : ℝ) (d : ℕ) : chi a d none = 0 := rfl

lemma mu_mul (a : ℝ) (d : ℕ) (ha : 0 < a) :
    a ^ d * mu a d = 1 + ∑ j ∈ Finset.range (d + 1), a ^ j := by
  unfold mu; field_simp

lemma mu_ge (a : ℝ) (d : ℕ) (ha : 0 < a) (ha1 : a ≤ 1) :
    1 + ∑ j ∈ Finset.range (d + 1), a ^ j ≤ mu a d := by
  have hpos : 0 < a ^ d := pow_pos ha d
  have hle : a ^ d ≤ 1 := pow_le_one₀ ha.le ha1
  have hS : 0 ≤ 1 + ∑ j ∈ Finset.range (d + 1), a ^ j := by positivity
  rw [← mu_mul a d ha]
  nlinarith [mu_mul a d ha]

lemma mu_pos (a : ℝ) (d : ℕ) (ha : 0 < a) (ha1 : a ≤ 1) : 1 ≤ mu a d := by
  have := mu_ge a d ha ha1
  have : 0 ≤ ∑ j ∈ Finset.range (d + 1), a ^ j := by positivity
  linarith

lemma chi_nonneg (a : ℝ) (d : ℕ) (ha : 0 < a) (ha1 : a ≤ 1) (o : Option ℕ) : 0 ≤ chi a d o := by
  rcases o with _ | i
  · simp [chi]
  · simp only [chi, sub_nonneg]
    have h1 : a ^ d ≤ a ^ (d - i) := pow_le_pow_of_le_one ha.le ha1 (Nat.sub_le d i)
    have hpos : 0 < a ^ d := pow_pos ha d
    have hmu : 0 ≤ mu a d := by linarith [mu_pos a d ha ha1]
    have h2 : ∑ j ∈ Finset.range (d - i + 1), a ^ j ≤ ∑ j ∈ Finset.range (d + 1), a ^ j :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.mpr (by omega))
        (fun j _ _ => by positivity)
    have h3 : a ^ d * mu a d ≤ a ^ (d - i) * mu a d := mul_le_mul_of_nonneg_right h1 hmu
    rw [mu_mul a d ha] at h3
    linarith

lemma chi_le (a : ℝ) (d : ℕ) (ha : 0 < a) (ha1 : a ≤ 1) (o : Option ℕ) : chi a d o ≤ mu a d := by
  rcases o with _ | i
  · simp [chi]; linarith [mu_pos a d ha ha1]
  · simp only [chi]
    have h1 : a ^ (d - i) ≤ 1 := pow_le_one₀ ha.le ha1
    have hmu : 0 ≤ mu a d := by linarith [mu_pos a d ha ha1]
    have h2 : 0 ≤ ∑ j ∈ Finset.range (d - i + 1), a ^ j := by positivity
    nlinarith

lemma chi_zero (a : ℝ) (d : ℕ) (ha : 0 < a) : chi a d (some 0) = 1 := by
  simp only [chi, Nat.sub_zero]
  rw [mu_mul a d ha]; ring

lemma chi_ge (a : ℝ) (d i : ℕ) (hi : d ≤ i) : chi a d (some i) = mu a d - 1 := by
  simp [chi, Nat.sub_eq_zero_of_le hi]

lemma chi_succ (a : ℝ) (d i : ℕ) (hi : i < d) :
    1 + chi a d (some i) = a * chi a d (some (i + 1)) := by
  simp only [chi]
  obtain ⟨m, hm⟩ : ∃ m, d - i = m + 1 := ⟨d - (i + 1), by omega⟩
  have hm2 : d - (i + 1) = m := by omega
  rw [hm, hm2, Finset.sum_range_succ' _ (m + 1), pow_succ, mul_sub, Finset.mul_sum]
  have : ∀ j ∈ Finset.range (m + 1), a ^ (j + 1) = a * a ^ j := fun j _ => by ring
  rw [Finset.sum_congr rfl this]
  ring

/-! ### One-step potential bookkeeping -/

lemma step_ineq_other (a : ℝ) (d : ℕ) (ha : 0 < a) (ha1 : a ≤ 1) (x y : ℕ → Bool) (act : Action)
    (c : Cfg) (h : ¬ (c.halted = none ∧ act = .attempt ∧ ∃ i, c.pos = some i ∧ i < d)) :
    mu a d * ((step d x y act c).tgtUsed : ℝ) + chi a d (step d x y act c).pos
        + (c.hist.length : ℝ)
      ≤ ((step d x y act c).hist.length : ℝ) + (mu a d * (c.tgtUsed : ℝ) + chi a d c.pos) := by
  rcases c with ⟨hs, p, nu, tu, hl⟩
  rcases hl with _ | b
  · cases act
    · have := chi_nonneg a d ha ha1 p
      simp [step, chi_zero a d ha]; linarith
    · rcases p with _ | i
      · simp [step, chi_zero a d ha]; linarith
      · have hi : d ≤ i := by
          by_contra hlt; exact h ⟨rfl, rfl, i, rfl, by omega⟩
        simp [step, Nat.not_lt.mpr hi, chi_ge a d i hi]; linarith
    · simp [step]; linarith
    · simp [step]; linarith
  · simp [step]; linarith

lemma step_eq_nav (a : ℝ) (d : ℕ) (x y : ℕ → Bool) (c : Cfg) (i : ℕ) (hh : c.halted = none)
    (hp : c.pos = some i) (hi : i < d) :
    mu a d * ((step d x y .attempt c).tgtUsed : ℝ) + chi a d (step d x y .attempt c).pos
        + (c.hist.length : ℝ) + a * chi a d (some (i + 1))
      = ((step d x y .attempt c).hist.length : ℝ) + (mu a d * (c.tgtUsed : ℝ) + chi a d c.pos)
        + (if x c.navUsed then chi a d (some (i + 1)) else 0) := by
  have h1 := chi_succ a d i hi
  rcases c with ⟨hs, p, nu, tu, hl⟩
  simp only at hh hp
  subst hh hp
  cases hx : x nu <;> simp [step, hi, hx] at h1 ⊢ <;> linarith

/-! ### The navigation events -/

section Main
variable {W : Type} [MeasurableSpace W] (R : Rule W) (d : ℕ) (n : ℕ)

def Ev (k i : ℕ) : Set (Omega W) :=
  {ω | (run R d ω n).halted = none ∧ R.decide ω.1 (run R d ω n).hist = .attempt ∧
    (run R d ω n).pos = some i ∧ i < d ∧ (run R d ω n).navUsed = k}

noncomputable def Xf (a : ℝ) (ω : Omega W) : ENNReal :=
  ∑' p : ℕ × ℕ, (Ev R d n p.1 p.2 ∩ {ω | ω.2.1 p.1 = true}).indicator
    (fun _ => ENNReal.ofReal (chi a d (some (p.2 + 1)))) ω

noncomputable def Yf (a : ℝ) (ω : Omega W) : ENNReal :=
  ∑' p : ℕ × ℕ, (Ev R d n p.1 p.2).indicator
    (fun _ => ENNReal.ofReal a * ENNReal.ofReal (chi a d (some (p.2 + 1)))) ω

lemma measurableSet_Ev (k i : ℕ) : MeasurableSet (Ev R d n k i : Set (Omega W)) := by
  have : (Ev R d n k i : Set (Omega W)) =
      (fun ω : Omega W => (run R d ω n, R.decide ω.1 (run R d ω n).hist)) ⁻¹'
        {p : Cfg × Action | p.1.halted = none ∧ p.2 = .attempt ∧ p.1.pos = some i ∧ i < d ∧
          p.1.navUsed = k} := rfl
  rw [this]
  exact measurable_run_decide R d n (Set.to_countable _).measurableSet

lemma Ev_inv (k i : ℕ) (w : W) (x y : ℕ → Bool) (b : Bool) :
    ((w, (Function.update x k b, y)) : Omega W) ∈ Ev R d n k i ↔ (w, (x, y)) ∈ Ev R d n k i := by
  constructor
  · intro h
    have e := run_update R d w (Function.update x k b) y k (x k) n (le_of_eq h.2.2.2.2)
    rw [Function.update_idem, Function.update_eq_self] at e
    simp only [Ev, Set.mem_ofPred_eq] at h ⊢
    rw [e]; exact h
  · intro h
    have e := run_update R d w x y k b n (le_of_eq h.2.2.2.2)
    simp only [Ev, Set.mem_ofPred_eq] at h ⊢
    rw [e]; exact h

lemma XY_eval (a : ℝ) (ω : Omega W) :
    (∃ i, ω ∈ Ev R d n (run R d ω n).navUsed i ∧
      Xf R d n a ω = (if ω.2.1 (run R d ω n).navUsed then ENNReal.ofReal (chi a d (some (i + 1)))
        else 0) ∧
      Yf R d n a ω = ENNReal.ofReal a * ENNReal.ofReal (chi a d (some (i + 1)))) ∨
    ((∀ k i, ω ∉ Ev R d n k i) ∧ Xf R d n a ω = 0 ∧ Yf R d n a ω = 0) := by
  by_cases hc : ∃ i, ω ∈ Ev R d n (run R d ω n).navUsed i
  · obtain ⟨i, hi⟩ := hc
    have huniq : ∀ p : ℕ × ℕ, ω ∈ Ev R d n p.1 p.2 → p = ((run R d ω n).navUsed, i) := by
      rintro ⟨k, j⟩ hj
      have h1 := hj.2.2.1; have h2 := hj.2.2.2.2; have h3 := hi.2.2.1
      rw [h1] at h3; simp only [Option.some.injEq] at h3
      simp [h3, h2]
    left
    refine ⟨i, hi, ?_, ?_⟩
    · rw [Xf, tsum_eq_single ((run R d ω n).navUsed, i)]
      · by_cases hx : ω.2.1 (run R d ω n).navUsed = true
        · simp [Set.indicator, hi, hx]
        · simp [Set.indicator, hx]
      · intro p hp
        rw [Set.indicator_of_notMem]
        exact fun hm => hp (huniq p hm.1)
    · rw [Yf, tsum_eq_single ((run R d ω n).navUsed, i)]
      · simp [Set.indicator, hi]
      · intro p hp
        rw [Set.indicator_of_notMem]
        exact fun hm => hp (huniq p hm)
  · right
    have hn : ∀ k i, ω ∉ Ev R d n k i := by
      intro k i hm
      have := hm.2.2.2.2; subst this; exact hc ⟨i, hm⟩
    refine ⟨hn, ?_, ?_⟩
    · rw [Xf]; refine ENNReal.tsum_eq_zero.mpr fun p => Set.indicator_of_notMem
        (fun hm => hn p.1 p.2 hm.1) _
    · rw [Yf]; refine ENNReal.tsum_eq_zero.mpr fun p => Set.indicator_of_notMem
        (fun hm => hn p.1 p.2 hm) _

end Main

/-! ### The expectation step -/

section Expect
variable {W : Type} [MeasurableSpace W] (ν : Measure W) [IsProbabilityMeasure ν] (R : Rule W)
  {a : ℝ} (d : ℕ) {q : ℝ}

noncomputable def Aseq (a q : ℝ) (n : ℕ) : ENNReal :=
  ∫⁻ ω, ENNReal.ofReal (mu a d * ((run R d ω n).tgtUsed : ℝ) + chi a d (run R d ω n).pos)
    ∂(lawQ ν a q)

noncomputable def Bseq (a q : ℝ) (n : ℕ) : ENNReal :=
  ∫⁻ ω, ENNReal.ofReal ((run R d ω n).hist.length : ℝ) ∂(lawQ ν a q)

lemma meas1 (n : ℕ) (g : Cfg → ENNReal) : Measurable (fun ω : Omega W => g (run R d ω n)) :=
  (measurable_of_countable g).comp (measurable_run R d n)

lemma lawQ_prob (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    IsProbabilityMeasure (lawQ ν a q) := by
  have := bern_prob ha0 ha1
  have := bern_prob hq0 hq1
  unfold lawQ; infer_instance

lemma XY_integral (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (n : ℕ) :
    ∫⁻ ω, Xf R d n a ω ∂(lawQ ν a q) = ∫⁻ ω, Yf R d n a ω ∂(lawQ ν a q) := by
  have hm : ∀ k : ℕ, MeasurableSet {ω : Omega W | ω.2.1 k = true} := fun k =>
    measurableSet_eq_fun ((measurable_pi_apply k).comp (measurable_fst.comp measurable_snd))
      measurable_const
  unfold Xf Yf
  have h1 : ∀ p : ℕ × ℕ, AEMeasurable (fun ω => (Ev R d n p.1 p.2 ∩ {ω | ω.2.1 p.1 = true}).indicator
      (fun _ => ENNReal.ofReal (chi a d (some (p.2 + 1)))) ω) (lawQ ν a q) := fun p =>
    (measurable_const.indicator ((measurableSet_Ev R d n p.1 p.2).inter (hm p.1))).aemeasurable
  have h2 : ∀ p : ℕ × ℕ, AEMeasurable (fun ω => (Ev R d n p.1 p.2).indicator
      (fun _ => ENNReal.ofReal a * ENNReal.ofReal (chi a d (some (p.2 + 1)))) ω) (lawQ ν a q) :=
    fun p => (measurable_const.indicator (measurableSet_Ev R d n p.1 p.2)).aemeasurable
  rw [lintegral_tsum h1, lintegral_tsum h2]
  refine tsum_congr fun p => ?_
  rw [lintegral_indicator_const ((measurableSet_Ev R d n p.1 p.2).inter (hm p.1)),
    lintegral_indicator_const (measurableSet_Ev R d n p.1 p.2),
    lawQ_indep ν ha0 ha1 hq0 hq1 p.1 (measurableSet_Ev R d n p.1 p.2)
      (fun w x y b => Ev_inv R d n p.1 p.2 w x y b)]
  ring

lemma Bseq_ne_top (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (n : ℕ) :
    Bseq ν R d a q n ≠ ⊤ := by
  have := lawQ_prob ν ha0 ha1 hq0 hq1
  refine ne_top_of_le_ne_top (b := ∫⁻ _, ENNReal.ofReal (n : ℝ) ∂(lawQ ν a q)) ?_ ?_
  · simp
  · refine lintegral_mono fun ω => ENNReal.ofReal_le_ofReal ?_
    exact_mod_cast run_len_le R d ω n

lemma step_expect (ha : 0 < a) (ha1 : a ≤ 1) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (n : ℕ) :
    Aseq ν R d a q (n + 1) + Bseq ν R d a q n ≤ Bseq ν R d a q (n + 1) + Aseq ν R d a q n := by
  have hP := lawQ_prob ν ha.le ha1 hq0 hq1
  have hmu0 : 0 ≤ mu a d := by linarith [mu_pos a d ha ha1]
  have hchi := chi_nonneg a d ha ha1
  -- pointwise inequality
  have hpt : ∀ ω : Omega W,
      ENNReal.ofReal (mu a d * ((run R d ω (n + 1)).tgtUsed : ℝ) + chi a d (run R d ω (n + 1)).pos)
        + ENNReal.ofReal ((run R d ω n).hist.length : ℝ) + Yf R d n a ω
      ≤ ENNReal.ofReal ((run R d ω (n + 1)).hist.length : ℝ)
        + ENNReal.ofReal (mu a d * ((run R d ω n).tgtUsed : ℝ) + chi a d (run R d ω n).pos)
        + Xf R d n a ω := by
    intro ω
    have hA1 : 0 ≤ mu a d * ((run R d ω (n + 1)).tgtUsed : ℝ) + chi a d (run R d ω (n + 1)).pos :=
      add_nonneg (mul_nonneg hmu0 (Nat.cast_nonneg _)) (hchi _)
    have hA0 : 0 ≤ mu a d * ((run R d ω n).tgtUsed : ℝ) + chi a d (run R d ω n).pos :=
      add_nonneg (mul_nonneg hmu0 (Nat.cast_nonneg _)) (hchi _)
    rw [← ENNReal.ofReal_add hA1 (Nat.cast_nonneg _),
      ← ENNReal.ofReal_add (Nat.cast_nonneg _) hA0]
    rcases XY_eval R d n a ω with ⟨i, hi, hX, hY⟩ | ⟨hn, hX, hY⟩
    · obtain ⟨hh, hact, hp, hid, -⟩ := hi
      have heq := step_eq_nav a d ω.2.1 ω.2.2 (run R d ω n) i hh hp hid
      rw [hX, hY, run_succ, hact]
      rw [run_succ, hact] at hA1
      have hci := hchi (some (i + 1))
      rw [← ENNReal.ofReal_mul ha.le, ← ENNReal.ofReal_add (add_nonneg hA1 (Nat.cast_nonneg _))
        (mul_nonneg ha.le hci)]
      split_ifs with hx
      · rw [hx, if_pos rfl] at heq
        rw [← ENNReal.ofReal_add (add_nonneg (Nat.cast_nonneg _) hA0) hci]
        exact ENNReal.ofReal_le_ofReal (by linarith)
      · simp only [Bool.not_eq_true] at hx
        rw [hx] at heq
        simp only [Bool.false_eq_true, if_false, add_zero] at heq
        rw [add_zero]
        exact ENNReal.ofReal_le_ofReal (by linarith)
    · rw [hX, hY, add_zero, add_zero]
      refine ENNReal.ofReal_le_ofReal ?_
      have hnot : ¬ ((run R d ω n).halted = none ∧ R.decide ω.1 (run R d ω n).hist = .attempt ∧
          ∃ i, (run R d ω n).pos = some i ∧ i < d) := by
        rintro ⟨hh, hact, i, hp, hid⟩
        exact hn _ i ⟨hh, hact, hp, hid, rfl⟩
      have := step_ineq_other a d ha ha1 ω.2.1 ω.2.2 _ _ hnot
      rw [run_succ]
      linarith
  have h1 := lintegral_mono hpt (μ := lawQ ν a q)
  have hF1 := meas1 R d (n + 1) (fun c => ENNReal.ofReal (mu a d * (c.tgtUsed : ℝ) + chi a d c.pos))
  have hF0 := meas1 R d n (fun c => ENNReal.ofReal (mu a d * (c.tgtUsed : ℝ) + chi a d c.pos))
  have hG1 := meas1 R d (n + 1) (fun c => ENNReal.ofReal (c.hist.length : ℝ))
  have hG0 := meas1 R d n (fun c => ENNReal.ofReal (c.hist.length : ℝ))
  have hFG : Measurable fun ω : Omega W =>
      ENNReal.ofReal (mu a d * ((run R d ω (n + 1)).tgtUsed : ℝ) + chi a d (run R d ω (n + 1)).pos)
        + ENNReal.ofReal ((run R d ω n).hist.length : ℝ) := hF1.add hG0
  have hGF : Measurable fun ω : Omega W =>
      ENNReal.ofReal ((run R d ω (n + 1)).hist.length : ℝ)
        + ENNReal.ofReal (mu a d * ((run R d ω n).tgtUsed : ℝ) + chi a d (run R d ω n).pos) :=
    hG1.add hF0
  rw [lintegral_add_left hFG, lintegral_add_left hF1,
    lintegral_add_left hGF, lintegral_add_left hG1,
    XY_integral ν R d ha.le ha1 hq0 hq1 n] at h1
  have hYfin : ∫⁻ ω, Yf R d n a ω ∂(lawQ ν a q) ≠ ⊤ := by
    refine ne_top_of_le_ne_top (b := ∫⁻ _, ENNReal.ofReal (mu a d) ∂(lawQ ν a q)) (by simp) ?_
    refine lintegral_mono fun ω => ?_
    rcases XY_eval R d n a ω with ⟨i, -, -, hY⟩ | ⟨-, -, hY⟩
    · rw [hY, ← ENNReal.ofReal_mul ha.le]
      refine ENNReal.ofReal_le_ofReal ?_
      have := chi_le a d ha ha1 (some (i + 1))
      have := hchi (some (i + 1))
      nlinarith
    · rw [hY]; exact zero_le
  exact ENNReal.le_of_add_le_add_right hYfin h1

lemma A_le_B (ha : 0 < a) (ha1 : a ≤ 1) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (n : ℕ) :
    Aseq ν R d a q n ≤ Bseq ν R d a q n := by
  induction n with
  | zero => simp [Aseq, run, Cfg.init]
  | succ n ih =>
    have h := step_expect ν R d ha ha1 hq0 hq1 n
    have h2 : Aseq ν R d a q (n + 1) + Bseq ν R d a q n
        ≤ Bseq ν R d a q (n + 1) + Bseq ν R d a q n := h.trans (add_le_add_right ih _)
    exact ENNReal.le_of_add_le_add_right (Bseq_ne_top ν R d ha.le ha1 hq0 hq1 n) h2

theorem main (ha : 0 < a) (ha1 : a ≤ 1) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    ENNReal.ofReal (mu a d) * expTargets R ν a d q ≤ expCost R ν a d q := by
  have hmu0 : 0 ≤ mu a d := by linarith [mu_pos a d ha ha1]
  have hT : expTargets R ν a d q
      = ⨆ n, ∫⁻ ω, (((run R d ω n).tgtUsed : ℕ) : ENNReal) ∂(lawQ ν a q) := by
    unfold expTargets targetCount
    simp only [ENat.toENNReal_iSup, ENat.toENNReal_coe]
    refine lintegral_iSup (fun n => meas1 R d n (fun c => ((c.tgtUsed : ℕ) : ENNReal))) ?_
    refine monotone_nat_of_le_succ fun n ω => ?_
    simp only [run_succ]
    exact_mod_cast step_tgt_mono _ _ _ _ _
  rw [hT, ENNReal.mul_iSup]
  refine iSup_le fun n => ?_
  calc ENNReal.ofReal (mu a d) * ∫⁻ ω, (((run R d ω n).tgtUsed : ℕ) : ENNReal) ∂(lawQ ν a q)
      = ∫⁻ ω, ENNReal.ofReal (mu a d) * (((run R d ω n).tgtUsed : ℕ) : ENNReal) ∂(lawQ ν a q) :=
        (lintegral_const_mul' _ _ ENNReal.ofReal_ne_top).symm
    _ ≤ Aseq ν R d a q n := by
        refine lintegral_mono fun ω => ?_
        rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul hmu0]
        exact ENNReal.ofReal_le_ofReal (le_add_of_nonneg_right (chi_nonneg a d ha ha1 _))
    _ ≤ Bseq ν R d a q n := A_le_B ν R d ha ha1 hq0 hq1 n
    _ ≤ expCost R ν a d q := by
        refine lintegral_mono fun ω => ?_
        rw [ENNReal.ofReal_natCast]
        unfold cost
        have : (((run R d ω n).hist.length : ℕ∞) : ENNReal) ≤
            ((⨆ m, ((run R d ω m).hist.length : ℕ∞) : ℕ∞) : ENNReal) :=
          ENat.toENNReal_le.mpr (le_iSup (fun m => ((run R d ω m).hist.length : ℕ∞)) n)
        simpa using this

end Expect

end PR3L

open PhysReaudit in
theorem solution {W : Type} [MeasurableSpace W] (ν : Measure W) [IsProbabilityMeasure ν]
    (R : Rule W) {a : ℝ} {d : ℕ} (ha : 0 < a) (ha1 : a ≤ 1) {q : ℝ} (hq : q ∈ Set.Icc (0 : ℝ) 1) :
    ENNReal.ofReal (mu a d) * expTargets R ν a d q ≤ expCost R ν a d q :=
  PR3L.main ν R d ha ha1 hq.1 hq.2
