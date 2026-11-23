-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.bAct_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:10:35.228377+00:00
-- url     : https://prove2.me/submissions/635d96cd-6ce1-4bff-9384-aa8e6d4785e1

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_Permute
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_IsKUnitaryOfIsInfUnitary
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_BigRep

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
theorem _root_.solution (k : ℕ) (a b : Fin n) (F : Big n k M) (κ : Fin k → Fin n × Fin n) :
    (bAct E k a b F) κ = E a b (F κ) + ∑ i, (factorAd k i a b F) κ := by
  show coord k κ ((mAct E k a b + ∑ i, factorAd k i a b : Module.End ℂ (Big n k M)) F) =
    E a b (F κ) + ∑ i, coord k κ (factorAd k i a b F)
  rw [LinearMap.add_apply, map_add, LinearMap.sum_apply, map_sum]
  rfl
end ReciprocityTheory.ChartRestriction.DS
