-- Prove2me | solution 1 for ReciprocityTheory.ThetaSummability.Est.measurableEmbedding_tailSum
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:51:05.558947+00:00
-- url     : https://prove2.me/submissions/771542bd-bcf6-4e28-acc5-41c0b6c3277e

import Definitions.Def_ReciprocityTheory_ThetaSummability_TailSumEstimates_ConeDefs
import Definitions.Def_ReciprocityTheory_ThetaSummability_TailSumEstimates_ConeChange

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ThetaSummability ReciprocityTheory.ThetaSummability.Est
open MeasureTheory Finset
variable {r : ℕ}
namespace ReciprocityTheory.ThetaSummability.Est
theorem _root_.solution : MeasurableEmbedding (tailSum (r := r)) :=
  (tailSumEquiv r).measurableEmbedding
end ReciprocityTheory.ThetaSummability.Est
