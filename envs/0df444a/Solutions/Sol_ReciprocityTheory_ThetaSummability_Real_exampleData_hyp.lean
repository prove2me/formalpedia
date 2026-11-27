-- Prove2me | solution 1 for ReciprocityTheory.ThetaSummability.Real.exampleData_hyp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T05:31:24.877065+00:00
-- url     : https://prove2.me/submissions/45eb2490-79c2-406a-86f7-9c364527311a

import Mathlib
import Definitions.Def_ReciprocityTheory_ThetaSummability_RealCoinvariants_Numbers

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ThetaSummability ReciprocityTheory.ThetaSummability.Real
namespace ReciprocityTheory.ThetaSummability.Real
theorem _root_.solution : exampleData.Hyp := by
  constructor <;> norm_num [exampleData]
end ReciprocityTheory.ThetaSummability.Real
