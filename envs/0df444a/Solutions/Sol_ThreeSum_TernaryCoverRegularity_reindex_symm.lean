-- Prove2me | solution 1 for ThreeSum.TernaryCoverRegularity.reindex_symm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:56:50.738211+00:00
-- url     : https://prove2.me/submissions/c062d77d-14de-4408-9caf-962e61df07e4

import Definitions.Def_Submission_ThreeSum_TernaryCoverLocal
import Mathlib.Logic.Equiv.Fintype
import Mathlib.Tactic
import Definitions.Def_Submission_ThreeSum_TernaryCoverRegularity
import Theorems.Thm_ThreeSum_TernaryCoverRegularity_left_mapEdge
import Theorems.Thm_ThreeSum_TernaryCoverRegularity_right_mapEdge
import Theorems.Thm_ThreeSum_TernaryCoverRegularity_output_mapEdge
import Theorems.Thm_ThreeSum_HashFamily_hashMap_apply
attribute [local simp] ThreeSum.HashFamily.hashMap_apply


attribute [local simp] ThreeSum.TernaryCoverRegularity.left_mapEdge
attribute [local simp] ThreeSum.TernaryCoverRegularity.right_mapEdge
attribute [local simp] ThreeSum.TernaryCoverRegularity.output_mapEdge

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryCoverRegularity
open Finset TernaryJointType TernaryCoverLocal
variable {L : ℕ}
namespace ThreeSum.TernaryCoverRegularity
theorem _root_.solution (σ : Equiv.Perm (Fin L)) (w : TritWord L) :
    reindex σ.symm (reindex σ w) = w := by
  funext i
  simp [reindex]
end ThreeSum.TernaryCoverRegularity
