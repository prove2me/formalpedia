-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.coefTr_casimirK
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:10:49.210795+00:00
-- url     : https://prove2.me/submissions/8ec88156-1271-4f7d-ac74-56a82124c428

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_HidaSetting
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_TensorV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirAlgebra_CasimirKKhwVec
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirAlgebra_MulMulSubMulMulEqAdd
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_CasimirGapAtNoncompactWeight
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_KUnitB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_CoefAInnerEqZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_CoefBTensSubKStable

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS
variable {n : ℕ}
variable {D : Type*} [NormedAddCommGroup D] [InnerProductSpace ℂ D]
namespace ReciprocityTheory.ChartRestriction.DS
theorem _root_.solution (ε : Fin n → Bool) (A : Fin n → Fin n → Module.End ℂ (Fin n → D)) :
    casimirK ε (fun a b => coefTr (A a b)) = coefTr (casimirK ε A) := by
  refine LinearMap.ext fun u => ?_
  simp only [casimirK, coefTr, LinearMap.sum_apply, Module.End.mul_apply,
    LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply, map_sum]
end ReciprocityTheory.ChartRestriction.DS
