-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FreeQuotientRank.incU_apply_eq_lTensor
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T01:34:10.549031+00:00
-- url     : https://prove2.me/submissions/54d2761e-b56e-4eeb-ab73-4e3eaaa66456

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_Rationality_FiniteDetectStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_Rationality_FiniteDimensionalBaseSpan

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
open scoped TensorProduct
open TensorProduct
variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]
namespace ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
theorem _root_.solution (F : Type*) [Field F] [Algebra K F] (U : Submodule K V)
    (y : F ⊗[K] U) : incU F U y = LinearMap.lTensor F U.subtype y := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul a u => simp [incU]
  | add y z hy hz => simp only [map_add, hy, hz]
end ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
