-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.blockSphereMeasure_isProbability
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:49:59.704165+00:00
-- url     : https://prove2.me/submissions/2e3146a6-e8e3-4979-8f8d-34d2db71fa2f

import Definitions.Def_ReciprocityTheory_SemistableReduction_AevalIsWeightedHomogeneous
import Definitions.Def_ReciprocityTheory_SemistableReduction_RestBlockSubstIsMultiHomogeneous
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_sphereMeasure_isProbability

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.MultiplicativeHeights
open MeasureTheory MvPolynomial
namespace ReciprocityTheory.MultiplicativeHeights
theorem _root_.solution {B n : ℕ} (hn : 0 < n) :
    IsProbabilityMeasure (blockSphereProb B n) := by
  haveI := sphereMeasure_isProbability hn
  unfold blockSphereProb
  infer_instance
end ReciprocityTheory.MultiplicativeHeights
