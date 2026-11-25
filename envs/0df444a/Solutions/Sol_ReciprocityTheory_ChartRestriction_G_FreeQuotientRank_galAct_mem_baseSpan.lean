-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FreeQuotientRank.galAct_mem_baseSpan
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T13:29:17.780658+00:00
-- url     : https://prove2.me/submissions/38b64e02-3b2c-4afc-bf11-c208036c1881

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_Rationality_FunKerSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_Rationality_RationalityHolds
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_Rationality_DescPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_Rationality_FunKerPf
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FreeQuotientRank_lTensor_mkQ_galAct
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FreeQuotientRank_mem_baseSpan_iff


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
    (σ : K₂ ≃ₐ[K] K₂) {x : K₂ ⊗[K] V} (hx : x ∈ baseSpan K₂ U) : galAct σ x ∈ baseSpan K₂ U := by
  rw [mem_baseSpan_iff] at hx ⊢
  rw [lTensor_mkQ_galAct, hx, map_zero]
end ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
