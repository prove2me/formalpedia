-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L1.homF_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T13:37:04.706921+00:00
-- url     : https://prove2.me/submissions/46420221-8f6f-4753-897d-efb8aae8f960

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_RedVeluFun
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_RedVeluAlg
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_EisensteinRecursion
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_IsogenyFormulaInstance
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_RedSeries
import Theorems.Thm_Formalism_L2_Th1_A_CubeR_mem_range


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical
open Formalism.L2.Th1.CM Formalism.L2.Th1.F Polynomial
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.L1
namespace ReciprocityTheory.ChartRestriction.L1
theorem _root_.solution {u : ℂ → ℂ} {m : ℕ} {Q : ℂ[X]} (hQ : Q.natDegree ≤ m) {z t : ℂ}
    (h : u z = z ^ 2 * t) : homF u m Q z = z ^ (2 * m) * Q.eval t := by
  rw [Polynomial.eval_eq_sum_range' (Nat.lt_succ_of_le hQ), Finset.mul_sum, homF]
  refine Finset.sum_congr rfl fun i hi => ?_
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le (Nat.lt_succ_iff.1 (Finset.mem_range.1 hi))
  rw [h, Nat.add_sub_cancel_left]
  ring
end ReciprocityTheory.ChartRestriction.L1
