-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FreeQuotientRank.lTensor_mkQ_inclT
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T01:34:11.916275+00:00
-- url     : https://prove2.me/submissions/dd419253-73d1-44fa-8cf9-293f715042b0

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_Rationality_FiniteDetectStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_Rationality_FiniteDimensionalBaseSpan
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_FreeQuotientRank_inclT_tmul__4dfde58e6361

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
variable {Ω : Type*} [Field Ω] [Algebra K Ω]
namespace ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
theorem _root_.solution (K₁ : IntermediateField K Ω) (U : Submodule K V) (x : K₁ ⊗[K] V) :
    LinearMap.lTensor Ω U.mkQ (inclT K₁ V x) =
      LinearMap.rTensor (V ⧸ U) (fldIncl K₁) (LinearMap.lTensor K₁ U.mkQ x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a v => simp [inclT_tmul', fldIncl]
  | add y z hy hz => simp only [map_add, hy, hz]
end ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
