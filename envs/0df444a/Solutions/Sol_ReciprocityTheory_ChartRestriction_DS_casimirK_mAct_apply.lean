-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.casimirK_mAct_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:09:59.112969+00:00
-- url     : https://prove2.me/submissions/2ce8d600-f70e-4f35-8a66-c5d7c24130ab

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_BigRep
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_BigCasA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_BigCas
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_bcas_sum_apply
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_BigCasimir_mAct_apply
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_mAct_apply


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
variable {M : Type*} [NormedAddCommGroup M] [InnerProductSpace ℂ M] {ε : Fin n → Bool}
  {E : Fin n → Fin n → Module.End ℂ M} {V : Submodule ℂ M}
namespace ReciprocityTheory.ChartRestriction.DS
theorem _root_.solution (k : ℕ) (F : Big n k M) (κ : Fin k → Fin n × Fin n) :
    casimirK ε (mAct E k) F κ = casimirK ε E (F κ) := by
  unfold casimirK
  simp only [LinearMap.sum_apply, bcas_sum_apply, Module.End.mul_apply, mAct_apply]
end ReciprocityTheory.ChartRestriction.DS
