-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_ProjIdealFormValue_weight_blockWeight_apply_e50de9fe3a17
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:00:36.853347+00:00
-- url     : https://prove2.me/submissions/0ddf9812-fc52-4174-94ed-e26e8965247c

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsProjIdealFormValue
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PProjIdealFormValue

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.NumbersDVR
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
noncomputable section
open GroundTheory.Heights₂.Heights.NumbersDVR.ProjIdealFormValue
namespace GroundTheory.Heights₂.Heights.NumbersDVR.ProjIdealFormValue
theorem _root_.solution {K : Type*} [DecidableEq K] {ι : K → Type*} (m : (Σ k, ι k) →₀ ℕ)
    (k : K) : Finsupp.weight (blockWeight ι) m k = Finsupp.mapDomain Sigma.fst m k := by
  rw [Finsupp.weight_apply, Finsupp.mapDomain, Finsupp.sum, Finsupp.sum, Finset.sum_apply,
    Finsupp.finsetSum_apply]
  refine Finset.sum_congr rfl fun v _ => ?_
  by_cases h : v.1 = k
  · simp [blockWeight, h]
  · simp [blockWeight, Ne.symm h]
end GroundTheory.Heights₂.Heights.NumbersDVR.ProjIdealFormValue
