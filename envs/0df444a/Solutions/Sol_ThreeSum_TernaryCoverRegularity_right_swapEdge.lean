-- Prove2me | solution 1 for ThreeSum.TernaryCoverRegularity.right_swapEdge
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:53:08.930877+00:00
-- url     : https://prove2.me/submissions/f8879d1d-088b-4f50-b366-33bded399235

import Definitions.Def_Submission_ThreeSum_TernaryCoverLocal
import Mathlib.Logic.Equiv.Fintype
import Mathlib.Tactic
import Definitions.Def_Submission_ThreeSum_TernaryCoverRegularity

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryCoverRegularity
open Finset TernaryJointType TernaryCoverLocal
variable {L : ℕ}
namespace ThreeSum.TernaryCoverRegularity
theorem _root_.solution {α π : DigitType} (e : LocalEdge L α π) :
    right (swapEdge e) = left e := rfl
end ThreeSum.TernaryCoverRegularity
