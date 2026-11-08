-- Prove2me | solution 1 for QEC.Coding.ExpanderCodes.PK20.balancingLift_gt_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T11:29:48.410826+00:00
-- url     : https://prove2.me/submissions/c06da6c0-804a-4689-a820-e134df0c4522

import Definitions.Def_QEC_Coding_ExpanderCodes_ClassicalFactor
import Definitions.Def_QEC_Coding_ExpanderCodes_TwoStepBalancing
import Definitions.Def_QEC_Coding_ExpanderCodes_Tradeoff

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ExpanderCodes QEC.Coding.ExpanderCodes.PK20
open QEC.Coding
open QEC.Coding.BalancedProduct
namespace QEC.Coding.ExpanderCodes.PK20
theorem _root_.solution (alpha : ℝ) (q : Nat) :
    1 < balancingLift alpha q := by
  unfold balancingLift
  omega
end QEC.Coding.ExpanderCodes.PK20
