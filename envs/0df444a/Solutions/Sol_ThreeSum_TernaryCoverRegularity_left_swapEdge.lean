-- Prove2me | solution 1 for ThreeSum.TernaryCoverRegularity.left_swapEdge
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:53:07.933876+00:00
-- url     : https://prove2.me/submissions/bf3dd2ec-bcf2-4eb8-a9be-337cd884a8a6

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
    left (swapEdge e) = right e := rfl
end ThreeSum.TernaryCoverRegularity
