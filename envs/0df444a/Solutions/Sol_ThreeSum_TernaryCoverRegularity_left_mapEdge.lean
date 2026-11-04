-- Prove2me | solution 1 for ThreeSum.TernaryCoverRegularity.left_mapEdge
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:53:04.68625+00:00
-- url     : https://prove2.me/submissions/2eda7dae-20d8-4bff-9e69-f7c060d85d62

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
    (e : LocalEdge L α π) : left (mapEdge σ e) = reindex σ (left e) := rfl
end ThreeSum.TernaryCoverRegularity
