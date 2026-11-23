-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.zPlus_khw
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:14:08.450869+00:00
-- url     : https://prove2.me/submissions/726e17e3-5ec9-4f0d-a171-abe769115a77

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_DiscreteSeriesExistence_CFPrimeA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_LayerWeight
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_DiscreteSeriesExistence_CFPrimeB

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
variable {n : ℕ} {M : Type*} [AddCommGroup M] [Module ℂ M]
namespace ReciprocityTheory.ChartRestriction.DS
theorem _root_.solution {ε : Fin n → Bool} {E : Fin n → Fin n → Module.End ℂ M} {ν : Fin n → ℝ} {w : M}
    (hw : IsKHWVec ε E ν w) : zPlus ε E w = (∑ c ∈ plusIdx ε, ((ν c : ℝ) : ℂ)) • w := by
  unfold zPlus
  rw [LinearMap.sum_apply, Finset.sum_smul]
  exact Finset.sum_congr rfl fun c _ => hw.1 c
end ReciprocityTheory.ChartRestriction.DS
