-- Prove2me | solution 1 for ReciprocityTheory.GeometryOfNumbersTheory.form_sq_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T15:59:35.093711+00:00
-- url     : https://prove2.me/submissions/4bdee92e-01de-4e83-8b80-ac5070f7b75a

import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_SphericalMonomials_MonomSt
import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_PluriharmonicAnalysis_BergmanDefs
import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_SphericalMonomials_SupStMonoNormSqPos
import Theorems.Thm_ReciprocityTheory_GeometryOfNumbersTheory_sum_mono_sq_div
import Theorems.Thm_ReciprocityTheory_GeometryOfNumbersTheory_integral_form_sq
import Theorems.Thm_ReciprocityTheory_GeometryOfNumbersTheory_supSt_monoNormSq_pos

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
theorem _root_.solution (D n : ℕ) (c : (Fin (D + 1) → ℕ) → ℂ) (z : Fin (D + 1) → ℂ) :
    ‖∑ a ∈ Finset.Nat.antidiagonalTuple (D + 1) n, c a * monoC a z‖ ^ 2 ≤
      ((n + D).choose D : ℝ) * sqN z ^ n *
        ∫ w, ‖∑ a ∈ Finset.Nat.antidiagonalTuple (D + 1) n, c a * monoC a w‖ ^ 2
          ∂(sphProb (D + 1)) := by
  set T := Finset.Nat.antidiagonalTuple (D + 1) n
  have hN : ∀ a : Fin (D + 1) → ℕ, 0 < Real.sqrt (monoNormSq a) := fun a => Real.sqrt_pos.mpr (supSt_monoNormSq_pos a)
  have h1 : ‖∑ a ∈ T, c a * monoC a z‖ ≤
      ∑ a ∈ T, (‖c a‖ * Real.sqrt (monoNormSq a)) * (‖monoC a z‖ / Real.sqrt (monoNormSq a)) := by
    refine (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun a _ => ?_))
    rw [norm_mul]
    field_simp [(hN a).ne']
  have h2 := Finset.sum_mul_sq_le_sq_mul_sq T (fun a => ‖c a‖ * Real.sqrt (monoNormSq a))
    (fun a => ‖monoC a z‖ / Real.sqrt (monoNormSq a))
  have e1 : ∑ a ∈ T, (‖c a‖ * Real.sqrt (monoNormSq a)) ^ 2 = ∑ a ∈ T, ‖c a‖ ^ 2 * monoNormSq a := by
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [mul_pow, Real.sq_sqrt (supSt_monoNormSq_pos a).le]
  have e2 : ∑ a ∈ T, (‖monoC a z‖ / Real.sqrt (monoNormSq a)) ^ 2 = ∑ a ∈ T, ‖monoC a z‖ ^ 2 / monoNormSq a := by
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [div_pow, Real.sq_sqrt (supSt_monoNormSq_pos a).le]
  rw [e1, e2, sum_mono_sq_div] at h2
  rw [integral_form_sq]
  calc ‖∑ a ∈ T, c a * monoC a z‖ ^ 2
      ≤ (∑ a ∈ T, (‖c a‖ * Real.sqrt (monoNormSq a)) * (‖monoC a z‖ / Real.sqrt (monoNormSq a))) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) h1 2
    _ ≤ (∑ a ∈ T, ‖c a‖ ^ 2 * monoNormSq a) * (((n + D).choose D : ℝ) * sqN z ^ n) := h2
    _ = ((n + D).choose D : ℝ) * sqN z ^ n * ∑ a ∈ T, ‖c a‖ ^ 2 * monoNormSq a := by ring
end ReciprocityTheory.GeometryOfNumbersTheory
