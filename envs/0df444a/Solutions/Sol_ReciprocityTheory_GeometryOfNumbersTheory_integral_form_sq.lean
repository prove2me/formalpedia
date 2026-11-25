-- Prove2me | solution 1 for ReciprocityTheory.GeometryOfNumbersTheory.integral_form_sq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T15:48:29.835327+00:00
-- url     : https://prove2.me/submissions/ea9163d0-8fb7-4c92-9096-98d79bd684ea

import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_SphericalMonomials_MonomSt
import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_PluriharmonicAnalysis_BergmanDefs
import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_SphericalMonomials_SupStMonoNormSqPos
import Theorems.Thm_ReciprocityTheory_GeometryOfNumbersTheory_supSt_integrable
import Theorems.Thm_ReciprocityTheory_GeometryOfNumbersTheory_supSt_gram

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.GeometryOfNumbersTheory
open MeasureTheory
namespace ReciprocityTheory.GeometryOfNumbersTheory
theorem _root_.solution (D n : ℕ) (c : (Fin (D + 1) → ℕ) → ℂ) :
    ∫ z, ‖∑ a ∈ Finset.Nat.antidiagonalTuple (D + 1) n, c a * monoC a z‖ ^ 2 ∂(sphProb (D + 1)) =
      ∑ a ∈ Finset.Nat.antidiagonalTuple (D + 1) n, ‖c a‖ ^ 2 * monoNormSq a := by
  set T := Finset.Nat.antidiagonalTuple (D + 1) n
  have key : ∀ z, ((‖∑ a ∈ T, c a * monoC a z‖ ^ 2 : ℝ) : ℂ) =
      ∑ a ∈ T, ∑ b ∈ T, (starRingEnd ℂ (c a) * c b) * (starRingEnd ℂ (monoC a z) * monoC b z) := by
    intro z
    push_cast
    rw [← Complex.conj_mul', map_sum, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    rw [map_mul]
    ring
  have hI : ∫ z, ‖∑ a ∈ T, c a * monoC a z‖ ^ 2 ∂(sphProb (D + 1)) =
      (∫ z, ((‖∑ a ∈ T, c a * monoC a z‖ ^ 2 : ℝ) : ℂ) ∂(sphProb (D + 1))).re := by
    rw [integral_complex_ofReal, Complex.ofReal_re]
  have inner : ∀ a ∈ T, ∫ z, ∑ b ∈ T, (starRingEnd ℂ (c a) * c b) *
      (starRingEnd ℂ (monoC a z) * monoC b z) ∂(sphProb (D + 1)) =
      ((‖c a‖ ^ 2 * monoNormSq a : ℝ) : ℂ) := by
    intro a ha
    rw [integral_finset_sum _ (fun b _ => (supSt_integrable a b).const_mul _)]
    simp_rw [integral_const_mul, supSt_gram]
    simp only [mul_ite, mul_zero, Finset.sum_ite_eq, ha, if_true]
    rw [Complex.conj_mul']
    push_cast
    ring
  rw [hI]
  simp_rw [key]
  rw [integral_finset_sum _ (fun a _ => integrable_finset_sum _ (fun b _ => (supSt_integrable a b).const_mul _)),
    Finset.sum_congr rfl inner, ← Complex.ofReal_sum, Complex.ofReal_re]
end ReciprocityTheory.GeometryOfNumbersTheory
