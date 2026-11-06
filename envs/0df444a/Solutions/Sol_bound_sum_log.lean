-- Prove2me | solution 1 for bound_sum_log
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-05T22:35:37.580267+00:00
-- url     : https://prove2.me/submissions/70da37ef-3664-4ce5-9ded-50cde51d91d4

import Definitions.Def_PrimeNumberTheoremAnd_Wiener
import Theorems.Thm_gg_of_hh
import Theorems.Thm_gg_le_one
import Theorems.Thm_one_div_two_pi_mem_Ioo
import Theorems.Thm_hh_nonneg
import Theorems.Thm_hh_continuous
import Theorems.Thm_hh_deriv
import Theorems.Thm_pp_pos
import Theorems.Thm_sum_range_succ
import Theorems.Thm_sum_le_integral
import Theorems.Thm_hh_integrable_aux

set_option autoImplicit true
open Real BigOperators ArithmeticFunction MeasureTheory Filter Set FourierTransform LSeries
  Asymptotics SchwartzMap
open Complex hiding log
open scoped Topology
open scoped ContDiff
open scoped ComplexConjugate
variable {n : ℕ} {A a b c d u x y t σ' : ℝ} {ψ Ψ : ℝ → ℂ} {F G : ℂ → ℂ} {f : ℕ → ℂ} {𝕜 : Type}
  [RCLike 𝕜]

private theorem hh_antitone_aux {a : ℝ} (ha : a ∈ Ioo (-1) 1) :
    AntitoneOn (hh a) (Ioi 0) := by
  have hh'_nonpos {x : ℝ} : hh' a x ≤ 0 := by
    have := pp_pos ha (log x)
    simp only [hh', neg_mul, Left.neg_nonpos_iff, ge_iff_le]
    positivity
  have l1 x (hx : x ∈ interior (Ioi 0)) :
      HasDerivWithinAt (hh a) (hh' a x) (interior (Ioi 0)) x := by
    have : x ≠ 0 := by contrapose! hx ; simp [hx]
    exact (hh_deriv a this).hasDerivWithinAt
  apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ioi _) (hh_continuous _) l1
    (fun x _ => hh'_nonpos)

private theorem hh_integrable_direct (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    IntegrableOn (fun t ↦ a * hh b (t / c)) (Ici 0) :=
  (hh_integrable_aux ha hb hc).1

private theorem cancel_aux_direct {C : ℝ} {f g : ℕ → ℝ} (hf : 0 ≤ f) (hg : 0 ≤ g)
    (hf' : ∀ n, cumsum f n ≤ C * n) (hg' : Antitone g) (n : ℕ) :
    ∑ i ∈ Finset.range n, f i * g i ≤ g (n - 1) * (C * n) + (C * (↑(n - 1 - 1) + 1) * g 0
      - C * (↑(n - 1 - 1) + 1) * g (n - 1) -
    ((n - 1 - 1) • (C * g 0) - ∑ x ∈ Finset.range (n - 1 - 1), C * g (x + 1))) := by
  have l1 (n : ℕ) :
      (g n - g (n + 1)) * ∑ i ∈ Finset.range (n + 1), f i ≤ (g n - g (n + 1)) * (C * (n + 1)) := by
    apply mul_le_mul le_rfl (by simpa only [cumsum, Nat.cast_add, Nat.cast_one] using hf' (n + 1))
      (Finset.sum_nonneg (fun i _ => hf i)) ?_
    simp only [sub_nonneg] ; apply hg' ; simp
  have l2 (x : ℕ) : C * (↑(x + 1) + 1) - C * (↑x + 1) = C := by simp ; ring
  have l3 (n : ℕ) : 0 ≤ cumsum f n := Finset.sum_nonneg (fun i _ => hf i)
  convert_to ∑ i ∈ Finset.range n, (g i) • (f i) ≤ _
  · simp [mul_comm]
  rw [Finset.sum_range_by_parts, sub_eq_add_neg, ← Finset.sum_neg_distrib]
  simp_rw [← neg_smul, neg_sub, smul_eq_mul]
  apply _root_.add_le_add
  · exact mul_le_mul le_rfl (hf' n) (l3 n) (hg _)
  · apply Finset.sum_le_sum (fun n _ => l1 n) |>.trans
    have heq :
        (∑ i ∈ Finset.range (n - 1), (g i - g (i + 1)) * (C * (↑i + 1))) =
          ∑ i ∈ Finset.range (n - 1), (C * (↑i + 1)) • (g i - g (i + 1)) := by
      apply Finset.sum_congr rfl
      intro i hi
      simp [mul_comm]
    rw [heq, Finset.sum_range_by_parts]
    simp_rw [Finset.sum_range_sub', l2, smul_sub, smul_eq_mul, Finset.sum_sub_distrib,
      Finset.sum_const, Finset.card_range]
    ring_nf
    exact le_rfl

private theorem cancel_aux'_direct {C : ℝ} {f g : ℕ → ℝ} (hf : 0 ≤ f) (hg : 0 ≤ g)
    (hf' : ∀ n, cumsum f n ≤ C * n) (hg' : Antitone g) (n : ℕ) :
    ∑ i ∈ Finset.range n, f i * g i ≤
        C * n * g (n - 1)
      + C * cumsum g (n - 1 - 1 + 1)
      - C * (↑(n - 1 - 1) + 1) * g (n - 1) := by
  have := cancel_aux_direct hf hg hf' hg' n
  simp only [nsmul_eq_mul, ← Finset.mul_sum, sum_range_succ] at this
  convert this using 1 ; unfold cumsum ; ring

private theorem cancel_main_direct {C : ℝ} {f g : ℕ → ℝ} (hf : 0 ≤ f) (hg : 0 ≤ g)
    (hf' : ∀ n, cumsum f n ≤ C * n) (hg' : Antitone g) (n : ℕ) (hn : 2 ≤ n) :
    cumsum (f * g) n ≤ C * cumsum g n := by
  change (∑ i ∈ Finset.range n, f i * g i) ≤ C * cumsum g n
  refine (cancel_aux'_direct hf hg hf' hg' n).trans_eq ?_
  have hindex : n - 1 - 1 + 1 = n - 1 := by omega
  have hcast : (n : ℝ) = ↑(n - 1) + 1 := by
    exact_mod_cast (show n = (n - 1) + 1 by omega)
  have hcast' : (↑(n - 1 - 1) : ℝ) + 1 = ↑(n - 1) := by
    exact_mod_cast hindex
  have hsum : cumsum g n = cumsum g (n - 1) + g (n - 1) := by
    conv_lhs => rw [show n = (n - 1) + 1 by omega]
    simp [cumsum, Finset.sum_range_succ]
  rw [hindex, hcast', hcast, hsum]
  ring

private theorem cancel_main'_direct {C : ℝ} {f g : ℕ → ℝ} (hf : 0 ≤ f) (hf0 : f 0 = 0)
    (hg : 0 ≤ g) (hf' : ∀ n, cumsum f n ≤ C * n) (hg' : Antitone g) (n : ℕ) :
    cumsum (f * g) n ≤ C * cumsum g n := by
  cases n with
  | zero => simp [cumsum]
  | succ n =>
    cases n with
    | zero =>
      have hC : 0 ≤ C := by simpa [cumsum, hf0] using hf' 1
      simpa [cumsum, hf0] using mul_nonneg hC (hg 0)
    | succ n => exact cancel_main_direct hf hg hf' hg' (n + 2) (by omega)

theorem solution {C : ℝ} (hf0 : f 0 = 0)
    (hf : (∀ n : ℕ, cumsum (fun k : ℕ ↦ ‖(f k : ℂ)‖) n ≤ C * n))
    {x : ℝ} (hx : 1 ≤ x) :
    ∑' i, ‖f i‖ / i * (1 + (1 / (2 * π) * log (i / x)) ^ 2)⁻¹ ≤
      C * (1 + ∫ t in Ioi 0, hh (1 / (2 * π)) t) := by
  let ggg (i : ℕ) : ℝ := if i = 0 then 1 else gg x i
  have l0 : x ≠ 0 := by linarith
  have l1 i : 0 ≤ ggg i := by by_cases hi : i = 0 <;> simp only [gg, one_div, mul_inv_rev, hi,
    ↓reduceIte, zero_le_one, ggg] ; positivity
  have l2 : Antitone ggg := by
    intro i j hij ; by_cases hi : i = 0 <;> by_cases hj : j = 0 <;> simp only [hj, ↓reduceIte, hi,
      le_refl, ggg]
    · exact gg_le_one _
    · omega
    · simp only [gg_of_hh l0]
      gcongr
      apply hh_antitone_aux one_div_two_pi_mem_Ioo
      · simp only [mem_Ioi] ; positivity
      · simp only [mem_Ioi] ; positivity
      · gcongr
  have l3 : 0 ≤ C := by simpa [cumsum, hf0] using hf 1
  have l4 : 0 ≤ ∫ (t : ℝ) in Ioi 0, hh (π⁻¹ * 2⁻¹) t :=
    setIntegral_nonneg measurableSet_Ioi (fun x hx => hh_nonneg _ (LT.lt.le hx))
  have l5 {n : ℕ} : AntitoneOn (fun t ↦ x⁻¹ * hh (1 / (2 * π)) (t / x)) (Ioc 0 n) := by
    intro u hu v hv huv
    have hu1 := hu.1
    have hv1 := hv.1
    simp only
    apply mul_le_mul le_rfl ?_ (hh_nonneg _ (by positivity)) (by positivity)
    apply hh_antitone_aux one_div_two_pi_mem_Ioo (by simp only [mem_Ioi] ; positivity)
      (by simp only [mem_Ioi] ; positivity)
    apply (div_le_div_iff_of_pos_right (by positivity)).mpr huv
  have l6 {n : ℕ} : IntegrableOn (fun t ↦ x⁻¹ * hh (π⁻¹ * 2⁻¹) (t / x)) (Icc 0 n) volume := by
    apply IntegrableOn.mono_set
      (hh_integrable_direct (by positivity) (by positivity) (by positivity)) Icc_subset_Ici_self
  apply Real.tsum_le_of_sum_range_le (fun n => by positivity) ; intro n
  convert_to ∑ i ∈ Finset.range n, ‖f i‖ * ggg i ≤ _
  · congr ; ext i
    by_cases hi : i = 0
    · simp [hi, hf0]
    · simp only [gg, hi, ↓reduceIte, ggg]
      field_simp
  apply cancel_main'_direct (fun _ => norm_nonneg _) (by simp [hf0]) l1 hf l2 n |>.trans
  gcongr ; simp only [cumsum, gg_of_hh l0, one_div, mul_inv_rev, ggg]
  by_cases hn : n = 0
  · simp only [hn, Finset.range_zero, Finset.sum_empty] ; positivity
  replace hn : 0 < n := by omega
  have : Finset.range n = {0} ∪ Finset.Ico 1 n := by
    ext i ; simp ; by_cases hi : i = 0 <;> simp [hi, hn] ; omega
  simp only [this, Finset.singleton_union, Finset.mem_Ico, nonpos_iff_eq_zero, one_ne_zero,
    false_and, not_false_eq_true, Finset.sum_insert, ↓reduceIte, add_le_add_iff_left, ge_iff_le]
  have hsum :
      (∑ x_1 ∈ Finset.Ico 1 n,
        if x_1 = 0 then 1 else x⁻¹ * hh (π⁻¹ * 2⁻¹) (↑x_1 / x)) =
        ∑ x_1 ∈ Finset.Ico 1 n, x⁻¹ * hh (π⁻¹ * 2⁻¹) (↑x_1 / x) := by
    apply Finset.sum_congr rfl
    intro i hi
    simp at hi
    have : i ≠ 0 := by omega
    simp [this]
  rw [hsum]
  simp_rw [Finset.sum_Ico_eq_sum_range, add_comm 1]
  have := @sum_le_integral 0 (fun t => x⁻¹ * hh (π⁻¹ * 2⁻¹) (t / x)) (n - 1)
    (by simpa using l5) (by simpa using l6)
  simp only [zero_add] at this
  apply this.trans
  rw [@intervalIntegral.integral_comp_div ℝ _ _ 0 ↑(n - 1) x (fun t => x⁻¹ * hh (π⁻¹ * 2⁻¹) (t)) l0]
  simp only [zero_div, intervalIntegral.integral_const_mul, smul_eq_mul, ← mul_assoc,
    mul_inv_cancel₀ l0, one_mul]
  have : (0 : ℝ) ≤ ↑(n - 1) / x := by positivity
  rw [intervalIntegral.intervalIntegral_eq_integral_uIoc]
  simp only [this, ↓reduceIte, uIoc_of_le, smul_eq_mul, one_mul, ge_iff_le]
  apply integral_mono_measure
  · apply Measure.restrict_mono Ioc_subset_Ioi_self le_rfl
  · apply eventually_of_mem (self_mem_ae_restrict measurableSet_Ioi)
    intro x (hx : 0 < x)
    apply hh_nonneg _ hx.le
  · have h := (@hh_integrable_direct 1 (1 / (2 * π)) 1 (by positivity) (by positivity) (by positivity))
    have h' := h.mono_set Ioi_subset_Ici_self
    unfold IntegrableOn at h'
    apply h'.congr
    exact Eventually.of_forall (fun t => by simp)
