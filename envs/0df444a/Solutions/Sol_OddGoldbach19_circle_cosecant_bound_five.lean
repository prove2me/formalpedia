-- Prove2me | solution 1 for OddGoldbach19.circle_cosecant_bound_five
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-30T16:44:02.515285+00:00
-- url     : https://prove2.me/submissions/ca52a5ac-d5e8-41b7-8c3d-409a669f6856

import Theorems.Thm_OddGoldbach19_cosecant_bound_of_cotangent_sharp
import Theorems.Thm_WeightedHilbert_cotangent_bound_of_real
import Theorems.Thm_Zeta23_MV_eigen_bound
import Theorems.Thm_Zeta23_MV_mvDiag_of_eigenBound
set_option autoImplicit false


set_option autoImplicit false
open scoped BigOperators ComplexConjugate
open OddGoldbach19

theorem solution {ι : Type} [Fintype ι] [DecidableEq ι]
    (θ δ : ι → ℝ) (v : ι → ℂ)
    (hpos : ∀ r, 0 < δ r) (hunit : ∀ r, δ r ≤ 1)
    (hgap : ∀ r s, r ≠ s → ∀ m : ℤ, δ r ≤ |θ r - θ s + m|) :
    ‖∑ r, ∑ s, if r = s then (0 : ℂ) else
      v r * conj (v s) /
        Complex.sin ((Real.pi : ℂ) * ((θ r - θ s : ℝ) : ℂ))‖ ≤
      5 * ∑ r, ‖v r‖ ^ 2 / δ r := by
  classical
  have hreal : Zeta23.MVDiag 13 := Zeta23.MV.mvDiag_of_eigenBound (by
    intro κ _ _ freq gap h u hu μ heig
    exact Zeta23.MV.eigen_bound h u hu μ heig)
  have h := cosecant_bound_of_cotangent_sharp 13
    (fun κ _ _ t gap a hp hu hg => WeightedHilbert_cotangent_bound_of_real 13 hreal t gap a hp hu hg)
    θ δ v hpos hunit hgap
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
    split_ifs <;> simp [div_eq_mul_inv] <;> ring
  rw [he, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos] at h
  have hm : 0 ≤ ∑ r, ‖v r‖ ^ 2 / δ r := Finset.sum_nonneg (fun r _ => div_nonneg (sq_nonneg _) (hpos r).le)
  have h13 : (13 : ℝ) * (∑ r, ‖v r‖ ^ 2 / δ r) ≤ Real.pi * (5 * ∑ r, ‖v r‖ ^ 2 / δ r) := by
    nlinarith [Real.pi_gt_three]
  exact (mul_le_mul_iff_right₀ Real.pi_pos).1 (h.trans h13)

#print axioms solution

