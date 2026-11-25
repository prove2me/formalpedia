-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FreeQuotientRank.lTensor_mkQ_galAct
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T13:00:08.098752+00:00
-- url     : https://prove2.me/submissions/957d84e3-bc6c-4be6-bca6-edfdc3715c03

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_Rationality_FunKerSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_Rationality_RationalityHolds
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_Rationality_DescPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_Rationality_FunKerPf

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
theorem _root_.solution {K₂ : Type*} [Field K₂] [Algebra K K₂] (U : Submodule K V)
    (σ : K₂ ≃ₐ[K] K₂) (x : K₂ ⊗[K] V) :
    LinearMap.lTensor K₂ U.mkQ (galAct σ x) =
      LinearMap.rTensor (V ⧸ U) σ.toLinearMap (LinearMap.lTensor K₂ U.mkQ x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a v => rfl
  | add y z hy hz => simp only [map_add, hy, hz]
end ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
