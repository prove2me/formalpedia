-- Prove2me | solution 1 for ThreeSum.TernaryCoverRegularity.output_mapEdge
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:53:06.851345+00:00
-- url     : https://prove2.me/submissions/c02afe35-774b-4585-b20c-6d32b2a96f23

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
    (e : LocalEdge L α π) : output (mapEdge σ e) = reindex σ (output e) := rfl
end ThreeSum.TernaryCoverRegularity
