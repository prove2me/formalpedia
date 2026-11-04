-- Prove2me | solution 1 for ThreeSum.TernaryCoverRegularity.right_mapEdge
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:53:05.806398+00:00
-- url     : https://prove2.me/submissions/b8f9b38c-236d-4c40-a429-c61ba0f8ee47

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
theorem _root_.solution (σ : Equiv.Perm (Fin L)) {α π : DigitType}
    (e : LocalEdge L α π) : right (mapEdge σ e) = reindex σ (right e) := rfl
end ThreeSum.TernaryCoverRegularity
