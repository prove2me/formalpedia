-- Prove2me | solution 1 for ScheduledQueue.Stability.ergodic_recurrence
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-24T22:47:44.217149+00:00
-- url     : https://prove2.me/submissions/c6af5c68-26cf-40d7-8416-18111bab4c92

import Mathlib
import Definitions.Def_ScheduledQueue_Stability_Setting
import Definitions.Def_ScheduledQueue_Stability_Reversed
import Theorems.Thm_ScheduledQueue_Stability_Y_gamma2_finite

open MeasureTheory ProbabilityTheory Set Filter Topology ENNReal

namespace SQErgAux

theorem sum_Icc_eq_range (f : ℕ → ℝ) (n : ℕ) :
    ∑ j ∈ Finset.Icc 1 n, f j = ∑ i ∈ Finset.range n, f (i + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ← ih, Finset.sum_Icc_succ_top (by omega)]

/-- Averages of a `[0,1]`-valued sequence converge if the averages along every residue class
modulo `m` converge to the same limit. -/
theorem mdep_avg (f : ℕ → ℝ) (hf0 : ∀ i, 0 ≤ f i) (hf1 : ∀ i, f i ≤ 1) (m : ℕ) (hm : 0 < m)
    (c : ℝ) (hr : ∀ r < m, Tendsto (fun K : ℕ => (K : ℝ)⁻¹ * ∑ k ∈ Finset.range K, f (k * m + r))
      atTop (𝓝 c)) :
    Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, f i) atTop (𝓝 c) := by
  set S : ℕ → ℝ := fun n => ∑ i ∈ Finset.range n, f i
  have hS : ∀ K, S (K * m) = ∑ r ∈ Finset.range m, ∑ k ∈ Finset.range K, f (k * m + r) := by
    intro K
    induction K with
    | zero => simp [S]
    | succ K ih =>
      simp only [S] at ih ⊢
      rw [show (K + 1) * m = K * m + m by ring, Finset.sum_range_add, ih, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun r _ => ?_
      rw [Finset.sum_range_succ]
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hA : Tendsto (fun K : ℕ => S (K * m) / (K * m : ℕ)) atTop (𝓝 c) := by
    have hsum : Tendsto (fun K : ℕ => (m : ℝ)⁻¹ * ∑ r ∈ Finset.range m,
        (K : ℝ)⁻¹ * ∑ k ∈ Finset.range K, f (k * m + r)) atTop (𝓝 ((m : ℝ)⁻¹ * ∑ r ∈ Finset.range m, c)) :=
      (tendsto_finset_sum _ fun r hr' => hr r (Finset.mem_range.1 hr')).const_mul _
    have hc : (m : ℝ)⁻¹ * ∑ r ∈ Finset.range m, c = c := by
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; field_simp
    rw [hc] at hsum
    refine hsum.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with K hK
    rw [hS, div_eq_inv_mul, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun r _ => ?_
    push_cast
    rw [mul_inv]; ring
  -- `K(n) = n / m`
  have hK : Tendsto (fun n : ℕ => n / m) atTop atTop := by
    rw [tendsto_atTop_atTop]
    intro b; refine ⟨b * m, fun n hn => ?_⟩
    exact (Nat.le_div_iff_mul_le hm).2 hn
  have hA' := hA.comp hK
  have hratio : Tendsto (fun n : ℕ => ((n / m * m : ℕ) : ℝ) / n) atTop (𝓝 1) := by
    have hup : ∀ n : ℕ, 0 < n → ((n / m * m : ℕ) : ℝ) / n ≤ 1 := by
      intro n hn
      rw [div_le_one (by exact_mod_cast hn)]
      exact_mod_cast Nat.div_mul_le_self n m
    have hlow : ∀ n : ℕ, 0 < n → 1 - (m : ℝ) / n ≤ ((n / m * m : ℕ) : ℝ) / n := by
      intro n hn
      have hnR : (0 : ℝ) < n := by exact_mod_cast hn
      have : (n : ℝ) - m ≤ ((n / m * m : ℕ) : ℝ) := by
        have h1 : n < n / m * m + m := Nat.lt_div_mul_add hm
        have : (n : ℝ) < ((n / m * m : ℕ) : ℝ) + m := by exact_mod_cast h1
        linarith
      rw [sub_div' (by positivity), div_le_div_iff_of_pos_right hnR]
      linarith
    have hmn : Tendsto (fun n : ℕ => 1 - (m : ℝ) / n) atTop (𝓝 1) := by
      have := (tendsto_const_div_atTop_nhds_zero_nat (m : ℝ)).const_sub 1
      simpa using this
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hmn tendsto_const_nhds ?_ ?_
    · filter_upwards [eventually_ge_atTop 1] with n hn using hlow n hn
    · filter_upwards [eventually_ge_atTop 1] with n hn using hup n hn
  have hrem : Tendsto (fun n : ℕ => (S n - S (n / m * m)) / n) atTop (𝓝 0) := by
    have hb : ∀ n : ℕ, 0 ≤ S n - S (n / m * m) ∧ S n - S (n / m * m) ≤ m := by
      intro n
      have hle : n / m * m ≤ n := Nat.div_mul_le_self n m
      have h1 : n < n / m * m + m := Nat.lt_div_mul_add hm
      generalize n / m * m = q at hle h1 ⊢
      obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hle
      have hdS : S n - S q = ∑ i ∈ Finset.range d, f (q + i) := by
        simp only [S]; rw [hd, Finset.sum_range_add]; ring
      rw [hdS]
      constructor
      · exact Finset.sum_nonneg fun i _ => hf0 _
      · calc ∑ i ∈ Finset.range d, f (q + i) ≤ ∑ i ∈ Finset.range d, (1 : ℝ) :=
              Finset.sum_le_sum fun i _ => hf1 _
          _ = d := by simp
          _ ≤ m := by exact_mod_cast (show d ≤ m by omega)
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
      (tendsto_const_div_atTop_nhds_zero_nat (m : ℝ)) ?_ ?_
    · exact Eventually.of_forall fun n => div_nonneg (hb n).1 (Nat.cast_nonneg n)
    · exact Eventually.of_forall fun n => div_le_div_of_nonneg_right (hb n).2 (Nat.cast_nonneg n)
  have hcomb := (hA'.mul hratio).add hrem
  rw [mul_one, add_zero] at hcomb
  refine hcomb.congr' ?_
  filter_upwards [eventually_ge_atTop m] with n hn
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (lt_of_lt_of_le hm hn)
  have hKpos : 0 < n / m * m := Nat.mul_pos (Nat.div_pos hn hm) hm
  have hKR : (0 : ℝ) < ((n / m * m : ℕ) : ℝ) := by exact_mod_cast hKpos
  simp only [Function.comp]
  field_simp
  ring

/-- The window of the last `m` perturbations before (and including) index `j`. -/
def win {Ω : Type*} (ξ : ℤ → Ω → ℝ) (m : ℕ) (j : ℤ) (ω : Ω) : Fin m → ℝ := fun k => ξ (j - k) ω

/-- Truncated version of `Y`: number of `k ∈ {1,…,m}` with `-u_{k-1} > (k-2)h`. -/
noncomputable def H (h : ℝ) (m : ℕ) (u : Fin m → ℝ) : ℝ :=
  ∑ k : Fin m, if ((k : ℝ) - 1) * h < -u k then 1 else 0

/-- Indicator that the truncated count is at most `l`. -/
noncomputable def G (h : ℝ) (m l : ℕ) (u : Fin m → ℝ) : ℝ := if H h m u ≤ l then 1 else 0

theorem measurable_H (h : ℝ) (m : ℕ) : Measurable (H h m) := by
  unfold H
  refine Finset.measurable_sum _ fun k _ => ?_
  exact Measurable.ite (measurableSet_lt measurable_const (measurable_pi_apply k).neg)
    measurable_const measurable_const

theorem measurable_G (h : ℝ) (m l : ℕ) : Measurable (G h m l) := by
  unfold G
  exact Measurable.ite (measurableSet_le (measurable_H h m) measurable_const)
    measurable_const measurable_const

theorem G_nonneg (h : ℝ) (m l : ℕ) (u : Fin m → ℝ) : 0 ≤ G h m l u := by
  unfold G; split_ifs <;> norm_num

theorem G_le_one (h : ℝ) (m l : ℕ) (u : Fin m → ℝ) : G h m l u ≤ 1 := by
  unfold G; split_ifs <;> norm_num

open ScheduledQueue.Stability

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {h : ℝ} {ξ : ℤ → Ω → ℝ} {U : Ω → ℝ}

theorem measurable_win (hin : ScheduledInput P ξ U) (m : ℕ) (j : ℤ) :
    Measurable (win ξ m j) :=
  measurable_pi_lambda _ fun k => hin.measurable _

theorem win_identDistrib (hin : ScheduledInput P ξ U) (m : ℕ) (j j' : ℤ) :
    IdentDistrib (win ξ m j) (win ξ m j') P P := by
  have hinj : ∀ c : ℤ, Function.Injective (fun k : Fin m => c - (k : ℤ)) := by
    intro c a b hab
    have : ((a : ℕ) : ℤ) = ((b : ℕ) : ℤ) := by simpa using hab
    exact Fin.ext (by exact_mod_cast this)
  exact IdentDistrib.pi (X := fun k : Fin m => ξ (j - k)) (Y := fun k : Fin m => ξ (j' - k))
    (fun k => (hin.identDistrib _).trans (hin.identDistrib _).symm)
    (hin.indep.precomp (hinj j)) (hin.indep.precomp (hinj j'))

theorem win_indep (hin : ScheduledInput P ξ U) (m : ℕ) (j j' : ℤ) (hjj : j + m ≤ j') :
    IndepFun (win ξ m j) (win ξ m j') P := by
  set S : Finset ℤ := Finset.univ.image (fun k : Fin m => j - (k : ℤ))
  set T : Finset ℤ := Finset.univ.image (fun k : Fin m => j' - (k : ℤ))
  have hST : Disjoint S T := by
    rw [Finset.disjoint_left]
    intro i hiS hiT
    simp only [S, T, Finset.mem_image, Finset.mem_univ, true_and] at hiS hiT
    obtain ⟨a, rfl⟩ := hiS
    obtain ⟨b, hb⟩ := hiT
    have ha := a.isLt
    have hb' := b.isLt
    omega
  have hind := hin.indep.indepFun_finset S T hST hin.measurable
  have hmemS : ∀ k : Fin m, j - (k : ℤ) ∈ S := fun k =>
    Finset.mem_image.2 ⟨k, Finset.mem_univ _, rfl⟩
  have hmemT : ∀ k : Fin m, j' - (k : ℤ) ∈ T := fun k =>
    Finset.mem_image.2 ⟨k, Finset.mem_univ _, rfl⟩
  have := hind.comp (φ := fun v : S → ℝ => fun k : Fin m => v ⟨j - k, hmemS k⟩)
    (ψ := fun v : T → ℝ => fun k : Fin m => v ⟨j' - k, hmemT k⟩)
    (measurable_pi_lambda _ fun k => measurable_pi_apply _)
    (measurable_pi_lambda _ fun k => measurable_pi_apply _)
  exact this

/-- Strong law for the `m`-dependent indicators `G(window_j)`. -/
theorem avg_G_tendsto (hin : ScheduledInput P ξ U) (m l : ℕ) (hm : 0 < m) :
    ∀ᵐ ω ∂P, Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n,
      G h m l (win ξ m ((i : ℤ) + 1) ω)) atTop (𝓝 (∫ ω, G h m l (win ξ m 0 ω) ∂P)) := by
  have hr : ∀ r : ℕ, ∀ᵐ ω ∂P, r < m → Tendsto (fun K : ℕ => (K : ℝ)⁻¹ * ∑ k ∈ Finset.range K,
      G h m l (win ξ m (((k * m + r : ℕ) : ℤ) + 1) ω)) atTop (𝓝 (∫ ω, G h m l (win ξ m 0 ω) ∂P)) := by
    intro r
    set X : ℕ → Ω → ℝ := fun k ω => G h m l (win ξ m (((k * m + r : ℕ) : ℤ) + 1) ω)
    have hXm : ∀ k, Measurable (X k) := fun k => (measurable_G h m l).comp (measurable_win hin m _)
    have hint : Integrable (X 0) P := by
      refine (integrable_const (1 : ℝ)).mono' (hXm 0).aestronglyMeasurable ?_
      exact Eventually.of_forall fun ω => by
        rw [Real.norm_eq_abs, abs_of_nonneg (G_nonneg _ _ _ _)]; exact G_le_one _ _ _ _
    have hindep : Pairwise (Function.onFun (fun f g => IndepFun f g P) X) := by
      have key : ∀ a b : ℕ, a < b → IndepFun (X a) (X b) P := by
        intro a b hab
        have hjj : (((a * m + r : ℕ) : ℤ) + 1) + m ≤ ((b * m + r : ℕ) : ℤ) + 1 := by
          have : a * m + m ≤ b * m := by nlinarith
          push_cast; omega
        exact (win_indep hin m _ _ hjj).comp (measurable_G h m l) (measurable_G h m l)
      intro a b hab
      rcases lt_or_gt_of_ne hab with h1 | h1
      · exact key a b h1
      · exact (key b a h1).symm
    have hident : ∀ k, IdentDistrib (X k) (X 0) P P := fun k =>
      (win_identDistrib hin m _ _).comp (measurable_G h m l)
    have hlaw := strong_law_ae X hint hindep hident
    have hmean : ∫ ω, X 0 ω ∂P = ∫ ω, G h m l (win ξ m 0 ω) ∂P :=
      ((win_identDistrib hin m _ _).comp (measurable_G h m l)).integral_eq
    filter_upwards [hlaw] with ω hω _
    rw [← hmean]
    simp only [smul_eq_mul] at hω; exact hω
  rw [← ae_all_iff] at hr
  filter_upwards [hr] with ω hω
  apply mdep_avg (fun i => G h m l (win ξ m ((i : ℤ) + 1) ω)) (fun _ => G_nonneg _ _ _ _)
    (fun _ => G_le_one _ _ _ _) m hm
  intro r hrm
  exact hω r hrm

theorem H_eq_card (m : ℕ) (u : Fin m → ℝ) :
    H h m u = ((Finset.univ.filter fun k : Fin m => ((k : ℝ) - 1) * h < -u k).card : ℝ) := by
  unfold H; rw [Finset.sum_boole]

omit [MeasurableSpace Ω] in
theorem rel_a (m l n : ℕ) (ω : Ω) (hY : Y h ξ n ω ≤ l) : H h m (win ξ m n ω) ≤ l := by
  rw [H_eq_card]
  set F := Finset.univ.filter fun k : Fin m => ((k : ℝ) - 1) * h < -win ξ m n ω k
  have hinj : Function.Injective (fun k : Fin m => (k : ℤ) + 1) := by
    intro a b hab; exact Fin.ext (by simpa using hab)
  have hsub : ((F.image fun k : Fin m => (k : ℤ) + 1) : Set ℤ) ⊆
      {k : ℤ | 1 ≤ k ∧ (k - 2) * h < -ξ ((n : ℤ) + 1 - k) ω} := by
    intro k' hk'
    simp only [Finset.coe_image, mem_image, Finset.mem_coe, F, Finset.mem_filter,
      Finset.mem_univ, true_and] at hk'
    obtain ⟨k, hk, rfl⟩ := hk'
    refine ⟨by omega, ?_⟩
    simp only [win] at hk
    have e : (n : ℤ) + 1 - ((k : ℤ) + 1) = (n : ℤ) - k := by ring
    rw [e]; push_cast; linarith
  have h1 : ((F.card : ℕ) : ℕ∞) ≤ Y h ξ n ω := by
    calc ((F.card : ℕ) : ℕ∞) = ((F.image fun k : Fin m => (k : ℤ) + 1) : Set ℤ).encard := by
          rw [Set.encard_coe_eq_coe_finsetCard, Finset.card_image_of_injective _ hinj]
      _ ≤ _ := encard_le_encard hsub
  have h2 : F.card ≤ l := by exact_mod_cast h1.trans hY
  exact_mod_cast h2

omit [MeasurableSpace Ω] in
theorem rel_b (m l n : ℕ) (ω : Ω) (hH : H h m (win ξ m n ω) ≤ l)
    (hT : ∀ k' : ℤ, (m : ℤ) < k' → ¬ (k' - 2) * h < -ξ ((n : ℤ) + 1 - k') ω) :
    Y h ξ n ω ≤ l := by
  rw [H_eq_card] at hH
  set F := Finset.univ.filter fun k : Fin m => ((k : ℝ) - 1) * h < -win ξ m n ω k
  have hsub : {k : ℤ | 1 ≤ k ∧ (k - 2) * h < -ξ ((n : ℤ) + 1 - k) ω} ⊆
      ((F.image fun k : Fin m => (k : ℤ) + 1) : Set ℤ) := by
    rintro k' ⟨hk1, hk2⟩
    have hkm : k' ≤ m := by
      by_contra hc; exact hT k' (by omega) hk2
    simp only [Finset.coe_image, mem_image, Finset.mem_coe, F, Finset.mem_filter,
      Finset.mem_univ, true_and]
    refine ⟨⟨(k' - 1).toNat, by omega⟩, ?_, by simp; omega⟩
    simp only [win]
    have e1 : (((⟨(k' - 1).toNat, by omega⟩ : Fin m) : ℕ) : ℤ) = k' - 1 := by simp; omega
    have e2 : ((((⟨(k' - 1).toNat, by omega⟩ : Fin m) : ℕ) : ℝ)) = (k' : ℝ) - 1 := by
      have : ((((⟨(k' - 1).toNat, by omega⟩ : Fin m) : ℕ) : ℤ) : ℝ) = ((k' - 1 : ℤ) : ℝ) := by
        rw [e1]
      push_cast at this; exact this
    rw [e2, e1]
    have e3 : (n : ℤ) - (k' - 1) = (n : ℤ) + 1 - k' := by ring
    rw [e3]; linarith
  have hF : F.card ≤ l := by exact_mod_cast hH
  calc Y h ξ n ω ≤ ((F.image fun k : Fin m => (k : ℤ) + 1) : Set ℤ).encard := encard_le_encard hsub
    _ = ((F.image fun k : Fin m => (k : ℤ) + 1).card : ℕ∞) := Set.encard_coe_eq_coe_finsetCard _
    _ ≤ (F.card : ℕ∞) := by exact_mod_cast Finset.card_image_le
    _ ≤ l := by exact_mod_cast hF

theorem bc_eventually_lt {h : ℝ} (hh : 0 < h) {W : Ω → ℝ} (hW : Integrable W P)
    (Z : ℕ → Ω → ℝ) (hZ : ∀ n, IdentDistrib (Z n) W P P) :
    ∀ᵐ ω ∂P, ∀ᶠ n : ℕ in atTop, Z n ω < n * h := by
  set X : Ω → ℝ := fun ω => max (W ω / h + 1) 0
  have hXint : Integrable X P := ((hW.div_const h).add (integrable_const 1)).pos_part
  have hX0 : 0 ≤ X := fun ω => le_max_right _ _
  have hfin : (∑' n : ℕ, P {ω | X ω ∈ Ioi (n : ℝ)}) < ∞ := by
    let _ : MeasureSpace Ω := ⟨P⟩
    exact tsum_prob_mem_Ioi_lt_top hXint hX0
  have hle : ∀ n : ℕ, P {ω | (n : ℝ) * h ≤ Z n ω} ≤ P {ω | X ω ∈ Ioi (n : ℝ)} := by
    intro n
    have e : P {ω | (n : ℝ) * h ≤ Z n ω} = P {ω | (n : ℝ) * h ≤ W ω} :=
      (hZ n).measure_mem_eq (s := {x | (n : ℝ) * h ≤ x}) (measurableSet_le measurable_const measurable_id)
    rw [e]
    apply measure_mono
    intro ω hω
    simp only [mem_setOf_eq, mem_Ioi, X] at hω ⊢
    have : (n : ℝ) ≤ W ω / h := by rw [le_div_iff₀ hh]; linarith
    exact lt_of_lt_of_le (by linarith) (le_max_left _ _)
  have hsum : (∑' n : ℕ, P {ω | (n : ℝ) * h ≤ Z n ω}) ≠ ∞ :=
    (lt_of_le_of_lt (ENNReal.tsum_le_tsum hle) hfin).ne
  filter_upwards [ae_eventually_notMem hsum] with ω hω
  filter_upwards [hω] with n hn
  simpa using hn

/-- Almost surely `-ξ_i ≤ B + |i| h` for all `i`, for some finite `B`. -/
theorem ae_linear_bound (hh : 0 < h) (hin : ScheduledInput P ξ U) :
    ∀ᵐ ω ∂P, ∃ B : ℝ, ∀ i : ℤ, -ξ i ω ≤ B + |(i : ℝ)| * h := by
  have h1 : ∀ᵐ ω ∂P, ∀ᶠ m : ℕ in atTop, -ξ (m : ℤ) ω < m * h := by
    apply bc_eventually_lt hh (W := fun ω => -ξ 0 ω) hin.integrable.neg
    intro m
    exact (hin.identDistrib _).comp (u := fun x : ℝ => -x) (by fun_prop)
  have h2 : ∀ᵐ ω ∂P, ∀ᶠ m : ℕ in atTop, -ξ (-(m : ℤ)) ω < m * h := by
    apply bc_eventually_lt hh (W := fun ω => -ξ 0 ω) hin.integrable.neg
    intro m
    exact (hin.identDistrib _).comp (u := fun x : ℝ => -x) (by fun_prop)
  filter_upwards [h1, h2] with ω h1 h2
  obtain ⟨N1, hN1⟩ := eventually_atTop.1 h1
  obtain ⟨N2, hN2⟩ := eventually_atTop.1 h2
  set N : ℕ := max N1 N2
  obtain ⟨B, hB⟩ : BddAbove ((fun i : ℤ => -ξ i ω) '' (Finset.Icc (-(N : ℤ)) N : Set ℤ)) :=
    ((Finset.finite_toSet _).image _).bddAbove
  refine ⟨max B 0, fun i => ?_⟩
  have habs : 0 ≤ |(i : ℝ)| * h := mul_nonneg (abs_nonneg _) hh.le
  by_cases hi : -(N : ℤ) ≤ i ∧ i ≤ N
  · have : -ξ i ω ≤ B := hB ⟨i, by simpa using hi, rfl⟩
    linarith [le_max_left B 0]
  · rcases le_or_gt 0 i with hi0 | hi0
    · have hm := hN1 i.toNat (by omega)
      have e : ((i.toNat : ℕ) : ℤ) = i := by omega
      have e2 : ((i.toNat : ℕ) : ℝ) = (i : ℝ) := by exact_mod_cast e
      rw [e, e2] at hm
      rw [abs_of_nonneg (by exact_mod_cast hi0)]
      linarith [le_max_right B 0]
    · have hm := hN2 (-i).toNat (by omega)
      have e : (-(((-i).toNat : ℕ) : ℤ)) = i := by omega
      have e2 : (((-i).toNat : ℕ) : ℝ) = -(i : ℝ) := by
        have : (((-i).toNat : ℕ) : ℤ) = -i := by omega
        exact_mod_cast this
      rw [e, e2] at hm
      rw [abs_of_neg (by exact_mod_cast hi0)]
      linarith [le_max_right B 0]

/-- The integrable dominating function for the tail counts. -/
noncomputable def gfun (h : ℝ) (m : ℕ) (x : ℝ) : ℝ := max (2 - m - x / h) 0

omit [MeasurableSpace Ω] [IsProbabilityMeasure P] in
theorem count_le (hh : 0 < h) (x : ℝ) (i : ℤ) (m n : ℕ) :
    (∑ j ∈ Finset.Icc 1 n, if (i + m ≤ (j : ℤ) ∧ ((j : ℝ) - i - 1) * h < -x) then (1 : ℝ) else 0)
      ≤ gfun h m x := by
  rw [Finset.sum_boole]
  set y : ℝ := 1 - m - x / h
  set F := (Finset.Icc 1 n).filter fun j : ℕ => (i + m ≤ (j : ℤ) ∧ ((j : ℝ) - i - 1) * h < -x)
  have hsub : F ⊆ (Finset.range ⌈y⌉₊).image (fun d : ℕ => (i + m + d).toNat) := by
    intro j hj
    simp only [F, Finset.mem_filter, Finset.mem_Icc] at hj
    obtain ⟨_, hj1, hj2⟩ := hj
    simp only [Finset.mem_image, Finset.mem_range]
    refine ⟨((j : ℤ) - i - m).toNat, ?_, by omega⟩
    apply Nat.lt_ceil.2
    have e : ((((j : ℤ) - i - m).toNat : ℕ) : ℝ) = (j : ℝ) - i - m := by
      have : ((((j : ℤ) - i - m).toNat : ℕ) : ℤ) = (j : ℤ) - i - m := by omega
      exact_mod_cast this
    rw [e]
    have : ((j : ℝ) - i - 1) < -x / h := by rw [lt_div_iff₀ hh]; linarith
    rw [neg_div] at this
    simp only [y]; linarith
  have hcard : (F.card : ℝ) ≤ ⌈y⌉₊ := by
    exact_mod_cast (Finset.card_le_card hsub).trans (Finset.card_image_le.trans (by simp))
  refine hcard.trans ?_
  unfold gfun
  rcases le_or_gt y 0 with hy | hy
  · rw [Nat.ceil_eq_zero.2 hy]; simp
  · have := Nat.ceil_lt_add_one hy.le
    refine le_trans this.le (le_max_of_le_left ?_)
    simp only [y]; linarith

/-- Tail event for the window `m` at time `n`. -/
def Tl (h : ℝ) (ξ : ℤ → Ω → ℝ) (m n : ℕ) (ω : Ω) : Prop :=
  ∃ k' : ℤ, (m : ℤ) < k' ∧ (k' - 2) * h < -ξ ((n : ℤ) + 1 - k') ω

omit [MeasurableSpace Ω] [IsProbabilityMeasure P] in
theorem tail_count (hh : 0 < h) (m : ℕ) (ω : Ω) (B : ℝ)
    (hB : ∀ i : ℤ, -ξ i ω ≤ B + |(i : ℝ)| * (h / 2)) (n : ℕ) :
    (∑ j ∈ Finset.Icc 1 n, by classical exact if Tl h ξ m j ω then (1 : ℝ) else 0) ≤
      (⌈B / h⌉₊ + 1 : ℕ) + ∑ i ∈ Finset.Icc 1 n, gfun h m (ξ i ω) := by
  classical
  set J0 : ℕ := ⌈B / h⌉₊ + 1
  set c : ℕ → ℕ → ℝ := fun i j =>
    if ((i : ℤ) + m ≤ (j : ℤ) ∧ ((j : ℝ) - (i : ℤ) - 1) * h < -ξ i ω) then 1 else 0
  have hc0 : ∀ i j, 0 ≤ c i j := fun i j => by simp only [c]; split_ifs <;> norm_num
  have hpt : ∀ j ∈ Finset.Icc 1 n, (if Tl h ξ m j ω then (1 : ℝ) else 0) ≤
      (if j < J0 then (1 : ℝ) else 0) + ∑ i ∈ Finset.Icc 1 n, c i j := by
    intro j hj
    simp only [Finset.mem_Icc] at hj
    have hsum0 : 0 ≤ ∑ i ∈ Finset.Icc 1 n, c i j := Finset.sum_nonneg fun i _ => hc0 i j
    by_cases hT : Tl h ξ m j ω
    · rw [if_pos hT]
      by_cases hjJ : j < J0
      · rw [if_pos hjJ]; linarith
      · rw [if_neg hjJ, zero_add]
        obtain ⟨k', hk'm, hk'⟩ := hT
        set i : ℤ := (j : ℤ) + 1 - k'
        have hi1 : 1 ≤ i := by
          by_contra hcon
          have hb := hB i
          have hi0 : (i : ℝ) ≤ 0 := by exact_mod_cast (show i ≤ 0 by omega)
          rw [abs_of_nonpos hi0] at hb
          have hiv : (i : ℝ) = (j : ℝ) + 1 - k' := by simp [i]
          have hjB : ((j : ℝ) - 1) * h < B := by nlinarith
          have hceil : B / h ≤ ⌈B / h⌉₊ := Nat.le_ceil _
          have : (j : ℝ) - 1 < B / h := by rw [lt_div_iff₀ hh]; linarith
          have : (j : ℝ) < J0 := by simp only [J0]; push_cast; linarith
          exact hjJ (by exact_mod_cast this)
        have hin : i.toNat ∈ Finset.Icc 1 n := by
          simp only [Finset.mem_Icc]; omega
        have hci : c i.toNat j = 1 := by
          simp only [c]
          rw [if_pos]
          have e : ((i.toNat : ℕ) : ℤ) = i := by omega
          rw [e]
          refine ⟨by omega, ?_⟩
          have e2 : ((j : ℝ) - ((i : ℤ) : ℝ) - 1) = (k' : ℝ) - 2 := by simp [i]; ring
          rw [e2]
          exact hk'
        rw [← hci]
        exact Finset.single_le_sum (fun i _ => hc0 i j) hin
    · rw [if_neg hT]
      have : (0 : ℝ) ≤ if j < J0 then 1 else 0 := by split_ifs <;> norm_num
      linarith
  calc (∑ j ∈ Finset.Icc 1 n, if Tl h ξ m j ω then (1 : ℝ) else 0)
      ≤ ∑ j ∈ Finset.Icc 1 n, ((if j < J0 then (1 : ℝ) else 0) + ∑ i ∈ Finset.Icc 1 n, c i j) :=
        Finset.sum_le_sum hpt
    _ = (∑ j ∈ Finset.Icc 1 n, if j < J0 then (1 : ℝ) else 0) +
          ∑ i ∈ Finset.Icc 1 n, ∑ j ∈ Finset.Icc 1 n, c i j := by
        rw [Finset.sum_add_distrib, Finset.sum_comm]
    _ ≤ (J0 : ℝ) + ∑ i ∈ Finset.Icc 1 n, gfun h m (ξ i ω) := by
        gcongr with i hi
        · rw [Finset.sum_boole]
          have : ((Finset.Icc 1 n).filter (fun j => j < J0)) ⊆ Finset.range J0 := by
            intro j hj; simp only [Finset.mem_filter] at hj; simpa using hj.2
          exact_mod_cast (Finset.card_le_card this).trans (by simp)
        · exact count_le hh (ξ i ω) i m n

theorem measurable_gfun (h : ℝ) (m : ℕ) : Measurable (gfun h m) := by
  unfold gfun; fun_prop

omit [MeasurableSpace Ω] [IsProbabilityMeasure P] in
theorem gfun_nonneg (m : ℕ) (x : ℝ) : 0 ≤ gfun h m x := le_max_right _ _

omit [MeasurableSpace Ω] [IsProbabilityMeasure P] in
theorem gfun_le (hh : 0 < h) (m : ℕ) (x : ℝ) : gfun h m x ≤ 2 + |x| / h := by
  unfold gfun
  apply max_le
  · have : -x / h ≤ |x| / h := div_le_div_of_nonneg_right (neg_le_abs x) hh.le
    have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    rw [neg_div] at this; linarith
  · positivity

theorem integrable_gfun (hh : 0 < h) (hin : ScheduledInput P ξ U) (m : ℕ) (i : ℤ) :
    Integrable (fun ω => gfun h m (ξ i ω)) P := by
  have hint : Integrable (ξ i) P := (hin.identDistrib i).integrable_iff.2 hin.integrable
  refine ((integrable_const (2 : ℝ)).add (hint.abs.div_const h)).mono'
    ((measurable_gfun h m).comp (hin.measurable i)).aestronglyMeasurable ?_
  exact Eventually.of_forall fun ω => by
    rw [Real.norm_eq_abs, abs_of_nonneg (gfun_nonneg m _)]
    exact gfun_le hh m _

theorem avg_gfun_tendsto (hh : 0 < h) (hin : ScheduledInput P ξ U) (m : ℕ) :
    ∀ᵐ ω ∂P, Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, gfun h m (ξ ((i : ℤ) + 1) ω))
      atTop (𝓝 (∫ ω, gfun h m (ξ 0 ω) ∂P)) := by
  set X : ℕ → Ω → ℝ := fun i ω => gfun h m (ξ ((i : ℤ) + 1) ω)
  have hindep : Pairwise (Function.onFun (fun f g => IndepFun f g P) X) := by
    intro a b hab
    exact (hin.indep.indepFun (show ((a : ℤ) + 1) ≠ (b : ℤ) + 1 by omega)).comp
      (measurable_gfun h m) (measurable_gfun h m)
  have hident : ∀ i, IdentDistrib (X i) (X 0) P P := fun i =>
    ((hin.identDistrib _).trans (hin.identDistrib _).symm).comp (measurable_gfun h m)
  have hlaw := strong_law_ae X (integrable_gfun hh hin m _) hindep hident
  have hmean : ∫ ω, X 0 ω ∂P = ∫ ω, gfun h m (ξ 0 ω) ∂P :=
    ((hin.identDistrib _).comp (measurable_gfun h m)).integral_eq
  filter_upwards [hlaw] with ω hω
  rw [← hmean]
  simp only [smul_eq_mul] at hω; exact hω

theorem gfun_mean_tendsto (hh : 0 < h) (hin : ScheduledInput P ξ U) :
    Tendsto (fun m : ℕ => ∫ ω, gfun h m (ξ 0 ω) ∂P) atTop (𝓝 0) := by
  have := tendsto_integral_of_dominated_convergence (μ := P)
    (F := fun (m : ℕ) ω => gfun h m (ξ 0 ω)) (f := fun _ => (0 : ℝ))
    (fun ω => gfun h 0 (ξ 0 ω))
    (fun m => ((measurable_gfun h m).comp (hin.measurable 0)).aestronglyMeasurable)
    (integrable_gfun hh hin 0 0)
    (fun m => Eventually.of_forall fun ω => by
      rw [Real.norm_eq_abs, abs_of_nonneg (gfun_nonneg m _)]
      unfold gfun
      apply max_le_max_right
      have : (0 : ℝ) ≤ m := Nat.cast_nonneg m
      simp only [Nat.cast_zero]; linarith)
    (Eventually.of_forall fun ω => by
      apply tendsto_const_nhds.congr'
      obtain ⟨M, hM⟩ := exists_nat_gt (2 - ξ 0 ω / h)
      filter_upwards [eventually_ge_atTop M] with m hm
      unfold gfun
      have : (M : ℝ) ≤ m := by exact_mod_cast hm
      rw [max_eq_right (by linarith)])
  simpa using this

omit [MeasurableSpace Ω] [IsProbabilityMeasure P] in
theorem H_win_eq (m : ℕ) (n : ℤ) (ω : Ω) :
    H h m (win ξ m n ω) = ∑ k ∈ Finset.range m, if ((k : ℝ) - 1) * h < -ξ (n - k) ω then 1 else 0 := by
  unfold H win
  exact Fin.sum_univ_eq_sum_range (fun k => if ((k : ℝ) - 1) * h < -ξ (n - k) ω then (1 : ℝ) else 0) m

omit [MeasurableSpace Ω] [IsProbabilityMeasure P] in
theorem H_win_mono {m m' : ℕ} (hmm : m ≤ m') (n : ℤ) (ω : Ω) :
    H h m (win ξ m n ω) ≤ H h m' (win ξ m' n ω) := by
  rw [H_win_eq, H_win_eq]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hmm)
    (fun k _ _ => by split_ifs <;> norm_num)

omit [MeasurableSpace Ω] [IsProbabilityMeasure P] in
/-- If all truncations stay below `l`, so does `Y_n`. -/
theorem rel_c (l n : ℕ) (ω : Ω) (hall : ∀ m : ℕ, H h m (win ξ m n ω) ≤ l) : Y h ξ n ω ≤ l := by
  by_contra hcon
  push Not at hcon
  have hle : ((l + 1 : ℕ) : ℕ∞) ≤ Y h ξ n ω := by
    have := Order.add_one_le_of_lt hcon
    exact_mod_cast this
  obtain ⟨T, hTsub, hTcard⟩ := Set.exists_subset_encard_eq hle
  have hTfin : T.Finite := Set.finite_of_encard_eq_coe hTcard
  obtain ⟨N, hN⟩ := hTfin.bddAbove
  set M : ℕ := N.toNat
  have hH := hall M
  rw [H_eq_card] at hH
  set F := Finset.univ.filter fun k : Fin M => ((k : ℝ) - 1) * h < -win ξ M n ω k
  have hsub : T ⊆ ((F.image fun k : Fin M => (k : ℤ) + 1) : Set ℤ) := by
    intro k' hk'
    obtain ⟨hk1, hk2⟩ := hTsub hk'
    have hkM : k' ≤ M := by have := hN hk'; omega
    simp only [Finset.coe_image, mem_image, Finset.mem_coe, F, Finset.mem_filter,
      Finset.mem_univ, true_and]
    refine ⟨⟨(k' - 1).toNat, by omega⟩, ?_, by simp; omega⟩
    simp only [win]
    have e1 : (((⟨(k' - 1).toNat, by omega⟩ : Fin M) : ℕ) : ℤ) = k' - 1 := by simp; omega
    have e2 : ((((⟨(k' - 1).toNat, by omega⟩ : Fin M) : ℕ) : ℝ)) = (k' : ℝ) - 1 := by
      have : ((((⟨(k' - 1).toNat, by omega⟩ : Fin M) : ℕ) : ℤ) : ℝ) = ((k' - 1 : ℤ) : ℝ) := by
        rw [e1]
      push_cast at this; exact this
    rw [e2, e1]
    have e3 : (n : ℤ) - (k' - 1) = (n : ℤ) + 1 - k' := by ring
    rw [e3]; linarith
  have h1 : ((l + 1 : ℕ) : ℕ∞) ≤ (F.card : ℕ∞) := by
    rw [← hTcard]
    calc T.encard ≤ ((F.image fun k : Fin M => (k : ℤ) + 1) : Set ℤ).encard := encard_le_encard hsub
      _ = ((F.image fun k : Fin M => (k : ℤ) + 1).card : ℕ∞) := Set.encard_coe_eq_coe_finsetCard _
      _ ≤ (F.card : ℕ∞) := by exact_mod_cast Finset.card_image_le
  have h2 : l + 1 ≤ F.card := by exact_mod_cast h1
  have h3 : (F.card : ℝ) ≤ l := hH
  have : ((l + 1 : ℕ) : ℝ) ≤ F.card := by exact_mod_cast h2
  push_cast at this; linarith

theorem pm_tendsto (hin : ScheduledInput P ξ U) (l : ℕ) :
    Tendsto (fun m : ℕ => ∫ ω, G h m l (win ξ m 0 ω) ∂P) atTop
      (𝓝 (P.real {ω | Y h ξ 0 ω ≤ l})) := by
  set E : Set Ω := {ω | Y h ξ 0 ω ≤ l}
  have hE : E = ⋂ m : ℕ, {ω | H h m (win ξ m 0 ω) ≤ l} := by
    ext ω
    simp only [E, mem_setOf_eq, mem_iInter]
    constructor
    · intro hY m
      have := rel_a (h := h) (ξ := ξ) m l 0 ω hY
      simpa using this
    · intro hall
      exact rel_c l 0 ω (fun m => by simpa using hall m)
  have hEm : MeasurableSet E := by
    rw [hE]
    exact MeasurableSet.iInter fun m =>
      measurableSet_le ((measurable_H h m).comp (measurable_win hin m 0)) measurable_const
  have hlim := tendsto_integral_of_dominated_convergence (μ := P)
    (F := fun (m : ℕ) ω => G h m l (win ξ m 0 ω)) (f := E.indicator (fun _ => (1 : ℝ)))
    (fun _ => (1 : ℝ))
    (fun m => ((measurable_G h m l).comp (measurable_win hin m 0)).aestronglyMeasurable)
    (integrable_const 1)
    (fun m => Eventually.of_forall fun ω => by
      rw [Real.norm_eq_abs, abs_of_nonneg (G_nonneg _ _ _ _)]; exact G_le_one _ _ _ _)
    (Eventually.of_forall fun ω => by
      by_cases hω : ω ∈ E
      · rw [indicator_of_mem hω]
        apply tendsto_const_nhds.congr'
        refine Eventually.of_forall fun m => ?_
        have := rel_a (h := h) (ξ := ξ) m l 0 ω hω
        simp only [Nat.cast_zero] at this
        simp only [G, this, if_true]
      · rw [indicator_of_notMem hω]
        have : ¬ ∀ m : ℕ, H h m (win ξ m 0 ω) ≤ l := by
          intro hall; exact hω (rel_c l 0 ω (fun m => by simpa using hall m))
        push Not at this
        obtain ⟨M, hM⟩ := this
        apply tendsto_const_nhds.congr'
        filter_upwards [eventually_ge_atTop M] with m hm
        have := H_win_mono (h := h) (ξ := ξ) hm 0 ω
        simp only [G]
        rw [if_neg (by linarith)])
  rw [show E.indicator (fun _ => (1 : ℝ)) = E.indicator 1 from rfl, integral_indicator_one hEm] at hlim
  exact hlim

end SQErgAux

open ScheduledQueue.Stability SQErgAux in
theorem solution {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (h : ℝ) (hh : 0 < h) (ξ : ℤ → Ω → ℝ) (U : Ω → ℝ)
    (hin : ScheduledInput P ξ U) :
    (∃ l : ℕ, 0 < P {ω | Y h ξ 0 ω ≤ l}) ∧
      ∀ l : ℕ, ∀ᵐ ω ∂P,
        Tendsto (fun n : ℕ => (n : ℝ)⁻¹ *
            ∑ j ∈ Finset.Icc 1 n, ({ω | Y h ξ j ω ≤ l}.indicator (fun _ => (1 : ℝ)) ω))
          atTop (𝓝 (P.real {ω | Y h ξ 0 ω ≤ l})) := by
  classical
  refine ⟨?_, ?_⟩
  · have hYG := Y_gamma2_finite P h hh ξ U hin
    by_contra hcon
    push Not at hcon
    have h0 : P (⋃ l : ℕ, {ω | Y h ξ 0 ω ≤ l}) = 0 :=
      measure_iUnion_null fun l => le_antisymm (hcon l) bot_le
    have hmem : ∀ᵐ ω ∂P, ω ∈ ⋃ l : ℕ, {ω | Y h ξ 0 ω ≤ l} := by
      filter_upwards [hYG] with ω ⟨hY, _⟩
      obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.1 (hY 0).ne
      exact mem_iUnion.2 ⟨m, by simp [← hm]⟩
    have hnot : ∀ᵐ ω ∂P, ω ∉ ⋃ l : ℕ, {ω | Y h ξ 0 ω ≤ l} := measure_eq_zero_iff_ae_notMem.1 h0
    have : ∀ᵐ ω ∂P, False := by
      filter_upwards [hmem, hnot] with ω h1 h2 using h2 h1
    obtain ⟨_, hfalse⟩ := this.exists
    exact hfalse
  intro l
  set p : ℝ := P.real {ω | Y h ξ 0 ω ≤ l}
  have hS1 : ∀ᵐ ω ∂P, ∀ m : ℕ, 0 < m → Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n,
      G h m l (win ξ m ((i : ℤ) + 1) ω)) atTop (𝓝 (∫ ω, G h m l (win ξ m 0 ω) ∂P)) := by
    rw [ae_all_iff]; intro m
    by_cases hm : 0 < m
    · filter_upwards [avg_G_tendsto (h := h) hin m l hm] with ω hω _ using hω
    · exact Eventually.of_forall fun ω h' => absurd h' hm
  have hS2 : ∀ᵐ ω ∂P, ∀ m : ℕ, Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n,
      gfun h m (ξ ((i : ℤ) + 1) ω)) atTop (𝓝 (∫ ω, gfun h m (ξ 0 ω) ∂P)) := by
    rw [ae_all_iff]; intro m; exact avg_gfun_tendsto hh hin m
  filter_upwards [hS1, hS2, ae_linear_bound (h := h / 2) (half_pos hh) hin] with ω h1 h2 ⟨B, hB⟩
  rw [Metric.tendsto_atTop]
  intro ε hε
  set δ : ℝ := ε / 8
  have hδ : 0 < δ := by positivity
  obtain ⟨m, hm1, hmp, hme⟩ : ∃ m : ℕ, 0 < m ∧ |∫ ω, G h m l (win ξ m 0 ω) ∂P - p| < δ ∧
      ∫ ω, gfun h m (ξ 0 ω) ∂P < δ := by
    have ha := (pm_tendsto (h := h) hin l).eventually (Metric.ball_mem_nhds p hδ)
    have hb := (gfun_mean_tendsto hh hin).eventually (gt_mem_nhds hδ)
    obtain ⟨m, hm⟩ := ((eventually_ge_atTop 1).and (ha.and hb)).exists
    exact ⟨m, hm.1, by simpa [Real.dist_eq] using hm.2.1, hm.2.2⟩
  set pm : ℝ := ∫ ω, G h m l (win ξ m 0 ω) ∂P
  set em : ℝ := ∫ ω, gfun h m (ξ 0 ω) ∂P
  set J0 : ℕ := ⌈B / h⌉₊ + 1
  have hem0 : 0 ≤ em := integral_nonneg fun ω => gfun_nonneg m _
  have hA := (Metric.tendsto_atTop.1 (h1 m hm1)) δ hδ
  have hBg := (Metric.tendsto_atTop.1 (h2 m)) δ hδ
  have hC := (Metric.tendsto_atTop.1 (tendsto_const_div_atTop_nhds_zero_nat (J0 : ℝ))) δ hδ
  obtain ⟨NA, hNA⟩ := hA
  obtain ⟨NB, hNB⟩ := hBg
  obtain ⟨NC, hNC⟩ := hC
  refine ⟨max (max NA NB) (max NC 1), fun n hn => ?_⟩
  have hnA := hNA n (by omega)
  have hnB := hNB n (by omega)
  have hnC := hNC n (by omega)
  have hn1 : 1 ≤ n := by omega
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn1
  rw [Real.dist_eq] at hnA hnB hnC ⊢
  set I : ℕ → ℝ := fun j => {ω | Y h ξ j ω ≤ l}.indicator (fun _ => (1 : ℝ)) ω
  set Gs : ℝ := ∑ i ∈ Finset.range n, G h m l (win ξ m ((i : ℤ) + 1) ω)
  set gs : ℝ := ∑ i ∈ Finset.range n, gfun h m (ξ ((i : ℤ) + 1) ω)
  have hGs : ∑ j ∈ Finset.Icc 1 n, G h m l (win ξ m (j : ℤ) ω) = Gs := by
    rw [sum_Icc_eq_range (fun j => G h m l (win ξ m (j : ℤ) ω))]; push_cast; rfl
  have hgs : ∑ j ∈ Finset.Icc 1 n, gfun h m (ξ (j : ℤ) ω) = gs := by
    rw [sum_Icc_eq_range (fun j => gfun h m (ξ (j : ℤ) ω))]; push_cast; rfl
  -- upper bound
  have hU : ∑ j ∈ Finset.Icc 1 n, I j ≤ Gs := by
    rw [← hGs]
    refine Finset.sum_le_sum fun j _ => ?_
    simp only [I]
    by_cases hY : Y h ξ j ω ≤ l
    · rw [indicator_of_mem (show ω ∈ {ω | Y h ξ j ω ≤ l} from hY)]
      simp only [G, rel_a m l j ω hY, if_true, le_refl]
    · rw [indicator_of_notMem (show ω ∉ {ω | Y h ξ j ω ≤ l} from hY)]
      exact G_nonneg _ _ _ _
  -- lower bound
  have hL : Gs ≤ ∑ j ∈ Finset.Icc 1 n, I j + ((J0 : ℝ) + gs) := by
    rw [← hGs, ← hgs]
    have htc := tail_count hh m ω B hB n
    have hpt : ∀ j ∈ Finset.Icc 1 n, G h m l (win ξ m (j : ℤ) ω) ≤
        I j + (if Tl h ξ m j ω then (1 : ℝ) else 0) := by
      intro j _
      have hI0 : 0 ≤ I j := by simp only [I]; exact indicator_nonneg (fun _ _ => zero_le_one) _
      by_cases hT : Tl h ξ m j ω
      · rw [if_pos hT]; linarith [G_le_one h m l (win ξ m (j : ℤ) ω)]
      · rw [if_neg hT, add_zero]
        by_cases hH : H h m (win ξ m j ω) ≤ l
        · have hY := rel_b m l j ω hH (fun k' hk' hk => hT ⟨k', hk', hk⟩)
          simp only [I, indicator_of_mem (show ω ∈ {ω | Y h ξ j ω ≤ l} from hY), G, hH, if_true,
            le_refl]
        · simp only [G, hH, if_false]; exact hI0
    calc ∑ j ∈ Finset.Icc 1 n, G h m l (win ξ m (j : ℤ) ω)
        ≤ ∑ j ∈ Finset.Icc 1 n, (I j + (if Tl h ξ m j ω then (1 : ℝ) else 0)) := Finset.sum_le_sum hpt
      _ = ∑ j ∈ Finset.Icc 1 n, I j + ∑ j ∈ Finset.Icc 1 n, (if Tl h ξ m j ω then (1 : ℝ) else 0) :=
          Finset.sum_add_distrib
      _ ≤ _ := by gcongr
  have hinv : 0 < (n : ℝ)⁻¹ := inv_pos.2 hnR
  have hU' : (n : ℝ)⁻¹ * ∑ j ∈ Finset.Icc 1 n, I j ≤ (n : ℝ)⁻¹ * Gs :=
    mul_le_mul_of_nonneg_left hU hinv.le
  have hL' : (n : ℝ)⁻¹ * Gs ≤ (n : ℝ)⁻¹ * ∑ j ∈ Finset.Icc 1 n, I j + ((J0 : ℝ) / n + (n : ℝ)⁻¹ * gs) := by
    have := mul_le_mul_of_nonneg_left hL hinv.le
    rw [mul_add, mul_add] at this
    rw [div_eq_inv_mul]; linarith
  have hJ : (J0 : ℝ) / n < δ := by
    have := hnC; rw [sub_zero, abs_of_nonneg (by positivity)] at this; exact this
  show |(n : ℝ)⁻¹ * ∑ j ∈ Finset.Icc 1 n, I j - p| < ε
  have hpmd : pm = ∫ ω, G h m l (win ξ m 0 ω) ∂P := rfl
  have hemd : em = ∫ ω, gfun h m (ξ 0 ω) ∂P := rfl
  have hδd : δ = ε / 8 := rfl
  rw [abs_lt] at hnA hnB hmp ⊢
  constructor <;> linarith

