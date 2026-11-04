-- Prove2me | solution 1 for ThreeSum.TernaryCoverGenericProjection.mixedFiber_generic_card_le_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:59:05.784201+00:00
-- url     : https://prove2.me/submissions/ad8f144c-dc45-456d-a057-0af43a602c76

import Definitions.Def_Submission_ThreeSum_TernaryProjectionCells
import Definitions.Def_Submission_ThreeSum_TernaryCoverLocal
import Mathlib.Tactic
import Definitions.Def_Submission_ThreeSum_TernaryCoverGenericProjection
import Theorems.Thm_ThreeSum_TernaryCoverGenericProjection_generic_cell_unique
import Theorems.Thm_ThreeSum_TernaryCoverLocal_edge_data
import Theorems.Thm_ThreeSum_TernaryCoverLocal_endpoint_injective


set_option autoImplicit false
set_option maxHeartbeats 0
noncomputable section
open ThreeSum ThreeSum.TernaryCoverGenericProjection
open Finset TernaryJointType TernaryCoverLocal
variable {K : Type*} [Field K]
variable {L p : ℕ}
namespace ThreeSum.TernaryCoverGenericProjection
theorem _root_.solution [Fact p.Prime] (α π : DigitType)
    {a b : ZMod p} (ha : a ≠ 0) (hb : b ≠ 0) (h2 : (2 : ZMod p) ≠ 0)
    (hsum : a+b ≠ 0) (heq : a ≠ b) (hhalf : 2*a ≠ b) (hdouble : a ≠ 2*b)
    (q : Fin L → ZMod p) : (mixedFiber α π a b q).card ≤ 1 := by
  classical
  apply card_le_one.mpr
  intro e he f hf
  have hpair (i : Fin L) : left e i = left f i ∧ right e i = right f i := by
    have h := ((mem_filter.mp he).2 i).trans ((mem_filter.mp hf).2 i).symm
    apply generic_cell_unique ha hb h2 hsum heq hhalf hdouble _ _ _ _ ?_ ?_ h
    · have hs := (edge_data e).2.2.2 i; have hq := (output e i).isLt; omega
    · have hs := (edge_data f).2.2.2 i; have hq := (output f i).isLt; omega
  apply endpoint_injective α π
  exact Prod.ext (funext fun i => (hpair i).1) (funext fun i => (hpair i).2)
end ThreeSum.TernaryCoverGenericProjection
