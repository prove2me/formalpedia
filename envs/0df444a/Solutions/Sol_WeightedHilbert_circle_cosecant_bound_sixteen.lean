-- Prove2me | solution 1 for WeightedHilbert_circle_cosecant_bound_sixteen
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-20T17:03:15.307977+00:00
-- url     : https://prove2.me/submissions/cd3fb5f4-c423-4051-9d88-9aa8b74db896

import Theorems.Thm_WeightedHilbert_cotangent_bound_of_real
import Theorems.Thm_Zeta23_MV_eigen_bound
import Theorems.Thm_Zeta23_MV_mvDiag_of_eigenBound
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Cotangent
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

set_option autoImplicit false
open scoped BigOperators ComplexConjugate
namespace WeightedHilbert

lemma csc_eq_cot_half_sub (z : ℂ) (hz : Complex.sin z ≠ 0) :
    (Complex.sin z)⁻¹ = Complex.cot (z / 2) - Complex.cot z := by
  have he : 2 * (z / 2) = z := by ring
  have hs : Complex.sin (z / 2) ≠ 0 := by
    intro h
    apply hz
    rw [← he, Complex.sin_two_mul, h]
    ring
  have hc : Complex.cos (z / 2) ≠ 0 := by
    intro h
    apply hz
    rw [← he, Complex.sin_two_mul, h]
    ring
  rw [Complex.cot_eq_cos_div_sin, Complex.cot_eq_cos_div_sin]
  conv_lhs => rw [← he, Complex.sin_two_mul]
  conv_rhs => rhs; rw [← he, Complex.cos_two_mul, Complex.sin_two_mul]
  field_simp
  ring

lemma sin_pi_mul_ne_zero_of_gap (x d : ℝ) (hd : 0 < d)
    (hgap : ∀ m : ℤ, d ≤ |x + m|) :
    Complex.sin ((Real.pi : ℂ) * (x : ℂ)) ≠ 0 := by
  rw [Complex.sin_ne_zero_iff]
  intro k hk
  have hp : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hx : (x : ℂ) = (k : ℂ) := by
    apply mul_left_cancel₀ hp
    calc
      (Real.pi : ℂ) * (x : ℂ) = (k : ℂ) * (Real.pi : ℂ) := hk
      _ = _ := mul_comm _ _
  have hx' : x = (k : ℝ) := by exact_mod_cast hx
  have h := hgap (-k)
  simp only [hx', Int.cast_neg, add_neg_cancel, abs_zero] at h
  exact (not_le_of_gt hd) h

lemma half_circular_gap {ι : Type} (θ δ : ι → ℝ)
    (hgap : ∀ r s, r ≠ s → ∀ m : ℤ, δ r ≤ |θ r - θ s + m|) :
    ∀ r s, r ≠ s → ∀ m : ℤ, δ r / 2 ≤ |θ r / 2 - θ s / 2 + m| := by
  intro r s hrs m
  have h := div_le_div_of_nonneg_right (hgap r s hrs (2*m)) (by norm_num : (0:ℝ) ≤ 2)
  calc
    δ r / 2 ≤ |θ r - θ s + (2*m : ℤ)| / 2 := h
    _ = |(θ r - θ s + (2*m : ℤ)) / 2| := by rw [abs_div]; norm_num
    _ = |θ r / 2 - θ s / 2 + m| := by congr 1; push_cast; ring

theorem cosecant_bound_of_cotangent (C : ℝ)
    (hCot : ∀ (κ : Type) [Fintype κ] [DecidableEq κ]
      (θ δ : κ → ℝ) (v : κ → ℂ),
      (∀ r, 0 < δ r) → (∀ r, δ r ≤ 1) →
      (∀ r s, r ≠ s → ∀ m : ℤ, δ r ≤ |θ r - θ s + m|) →
      ‖∑ r, ∑ s, if r = s then (0 : ℂ) else
        v r * conj (v s) * ((Real.pi : ℂ) *
          Complex.cot ((Real.pi : ℂ) * ((θ r - θ s : ℝ) : ℂ)))‖ ≤
        C * ∑ r, ‖v r‖ ^ 2 / δ r)
    {ι : Type} [Fintype ι] [DecidableEq ι] (θ δ : ι → ℝ) (v : ι → ℂ)
    (hpos : ∀ r, 0 < δ r) (hunit : ∀ r, δ r ≤ 1)
    (hgap : ∀ r s, r ≠ s → ∀ m : ℤ, δ r ≤ |θ r - θ s + m|) :
    ‖∑ r, ∑ s, if r = s then (0 : ℂ) else
      v r * conj (v s) * ((Real.pi : ℂ) *
        (Complex.sin ((Real.pi : ℂ) * ((θ r - θ s : ℝ) : ℂ)))⁻¹)‖ ≤
      (3 * C) * ∑ r, ‖v r‖ ^ 2 / δ r := by
  let F : (ι → ℝ) → ℂ := fun t => ∑ r, ∑ s, if r = s then 0 else
    v r * conj (v s) * ((Real.pi : ℂ) *
      Complex.cot ((Real.pi : ℂ) * ((t r - t s : ℝ) : ℂ)))
  have hfull : ‖F θ‖ ≤ C * ∑ r, ‖v r‖ ^ 2 / δ r :=
    hCot ι θ δ v hpos hunit hgap
  have hhalf : ‖F (fun r => θ r / 2)‖ ≤
      C * ∑ r, ‖v r‖ ^ 2 / (δ r / 2) :=
    hCot ι (fun r => θ r / 2) (fun r => δ r / 2) v
      (fun r => div_pos (hpos r) (by norm_num))
      (fun r => by linarith [hunit r]) (half_circular_gap θ δ hgap)
  have hmass : (∑ r, ‖v r‖ ^ 2 / (δ r / 2)) = 2 * ∑ r, ‖v r‖ ^ 2 / δ r := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro r hr
    ring
  rw [hmass] at hhalf
  have hform : (∑ r, ∑ s, if r = s then (0 : ℂ) else
      v r * conj (v s) * ((Real.pi : ℂ) *
        (Complex.sin ((Real.pi : ℂ) * ((θ r - θ s : ℝ) : ℂ)))⁻¹)) =
      F (fun r => θ r / 2) - F θ := by
    dsimp only [F]
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro r hr
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro s hs
    by_cases hrs : r = s
    · simp [hrs]
    · simp only [hrs, ↓reduceIte]
      rw [csc_eq_cot_half_sub _ (sin_pi_mul_ne_zero_of_gap _ _ (hpos r) (hgap r s hrs))]
      have he : (Real.pi : ℂ) * ((θ r / 2 - θ s / 2 : ℝ) : ℂ) =
          (Real.pi : ℂ) * ((θ r - θ s : ℝ) : ℂ) / 2 := by push_cast; ring
      rw [he]
      ring
  rw [hform]
  calc
    ‖F (fun r => θ r / 2) - F θ‖ ≤ ‖F (fun r => θ r / 2)‖ + ‖F θ‖ := norm_sub_le _ _
    _ ≤ C * (2 * ∑ r, ‖v r‖ ^ 2 / δ r) + C * ∑ r, ‖v r‖ ^ 2 / δ r := add_le_add hhalf hfull
    _ = (3 * C) * ∑ r, ‖v r‖ ^ 2 / δ r := by ring

theorem circle_bound_sixteen_of_cotangent
    (hCot : ∀ (κ : Type) [Fintype κ] [DecidableEq κ]
      (θ δ : κ → ℝ) (v : κ → ℂ),
      (∀ r, 0 < δ r) → (∀ r, δ r ≤ 1) →
      (∀ r s, r ≠ s → ∀ m : ℤ, δ r ≤ |θ r - θ s + m|) →
      ‖∑ r, ∑ s, if r = s then (0 : ℂ) else
        v r * conj (v s) * ((Real.pi : ℂ) *
          Complex.cot ((Real.pi : ℂ) * ((θ r - θ s : ℝ) : ℂ)))‖ ≤
        13 * ∑ r, ‖v r‖ ^ 2 / δ r)
    {ι : Type} [Fintype ι] [DecidableEq ι] (θ δ : ι → ℝ) (v : ι → ℂ)
    (hpos : ∀ r, 0 < δ r) (hunit : ∀ r, δ r ≤ 1)
    (hgap : ∀ r s, r ≠ s → ∀ m : ℤ, δ r ≤ |θ r - θ s + m|) :
    ‖∑ r, ∑ s, if r = s then (0 : ℂ) else
      v r * conj (v s) /
        Complex.sin ((Real.pi : ℂ) * ((θ r - θ s : ℝ) : ℂ))‖ ≤
      16 * ∑ r, ‖v r‖ ^ 2 / δ r := by
  have h := cosecant_bound_of_cotangent 13 hCot θ δ v hpos hunit hgap
  have he : (∑ r, ∑ s, if r = s then (0 : ℂ) else
      v r * conj (v s) * ((Real.pi : ℂ) *
        (Complex.sin ((Real.pi : ℂ) * ((θ r - θ s : ℝ) : ℂ)))⁻¹)) =
      (Real.pi : ℂ) * ∑ r, ∑ s, if r = s then (0 : ℂ) else
        v r * conj (v s) / Complex.sin ((Real.pi : ℂ) * ((θ r - θ s : ℝ) : ℂ)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro r hr
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro s hs
    by_cases hrs : r = s
    · simp [hrs]
    · simp only [hrs, ↓reduceIte, div_eq_mul_inv]; ring
  rw [he, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos] at h
  have hn : 0 ≤ ∑ r, ‖v r‖ ^ 2 / δ r :=
    Finset.sum_nonneg (fun r _ => div_nonneg (sq_nonneg _) (le_of_lt (hpos r)))
  have hp := Real.pi_gt_three
  have heq : (39 : ℝ) * (∑ r, ‖v r‖ ^ 2 / δ r) ≤
      Real.pi * (16 * ∑ r, ‖v r‖ ^ 2 / δ r) := by nlinarith
  apply (mul_le_mul_iff_right₀ Real.pi_pos).mp
  exact h.trans (by simpa only [show (3 : ℝ) * 13 = 39 by norm_num] using heq)

end WeightedHilbert

/-- A concrete circle Hilbert estimate obtained from the accepted real bound. -/
theorem solution {ι : Type} [Fintype ι] [DecidableEq ι]
    (θ δ : ι → ℝ) (v : ι → ℂ)
    (hpos : ∀ r, 0 < δ r) (hunit : ∀ r, δ r ≤ 1)
    (hgap : ∀ r s, r ≠ s → ∀ m : ℤ, δ r ≤ |θ r - θ s + m|) :
    ‖∑ r, ∑ s, if r = s then (0 : ℂ) else
      v r * conj (v s) /
        Complex.sin ((Real.pi : ℂ) * ((θ r - θ s : ℝ) : ℂ))‖ ≤
      16 * ∑ r, ‖v r‖ ^ 2 / δ r := by
  have hreal : Zeta23.MVDiag 13 := Zeta23.MV.mvDiag_of_eigenBound (by
    intro κ _ _ freq gap h u hu μ heig
    exact Zeta23.MV.eigen_bound h u hu μ heig)
  apply WeightedHilbert.circle_bound_sixteen_of_cotangent _ θ δ v hpos hunit hgap
  intro κ _ _ t gap a hpos hunit hgap
  exact WeightedHilbert_cotangent_bound_of_real 13 hreal t gap a hpos hunit hgap

#print axioms solution
