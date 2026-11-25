-- Prove2me | solution 1 for ReciprocityTheory.GeometryOfNumbersTheory.sum_mono_sq_div
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T14:18:18.183606+00:00
-- url     : https://prove2.me/submissions/34c1fb55-46eb-4c66-be28-3888395e567c

import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_SphericalMonomials_MonomSt
import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_PluriharmonicAnalysis_BergmanDefs
import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_SphericalMonomials_SupStMonoNormSqPos
import Theorems.Thm_ReciprocityTheory_GeometryOfNumbersTheory_supSt_adt_eq
import Theorems.Thm_ReciprocityTheory_GeometryOfNumbersTheory_supSt_term

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
theorem _root_.solution (D n : ℕ) (z : Fin (D + 1) → ℂ) :
    ∑ a ∈ Finset.Nat.antidiagonalTuple (D + 1) n, ‖monoC a z‖ ^ 2 / monoNormSq a =
      ((n + D).choose D : ℝ) * sqN z ^ n := by
  rw [Finset.sum_congr rfl (fun a ha => supSt_term a (Finset.Nat.mem_antidiagonalTuple.mp ha) z),
    ← Finset.mul_sum, supSt_adt_eq, sqN, Finset.sum_pow_eq_sum_piAntidiag]
end ReciprocityTheory.GeometryOfNumbersTheory
