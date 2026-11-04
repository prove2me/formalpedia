-- Prove2me | solution 1 for ThreeSum.TernaryCoverRegularity.swapEdge_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:34:58.884443+00:00
-- url     : https://prove2.me/submissions/404328de-2416-41e5-8b33-a629745c93fb

import Definitions.Def_Submission_ThreeSum_TernaryCoverLocal
import Mathlib.Logic.Equiv.Fintype
import Mathlib.Tactic
import Definitions.Def_Submission_ThreeSum_TernaryCoverRegularity
import Theorems.Thm_ThreeSum_TernaryCoverRegularity_swapEdge_swapEdge
import Theorems.Thm_ThreeSum_HashFamily_hashMap_apply
attribute [local simp] ThreeSum.HashFamily.hashMap_apply


attribute [local simp] ThreeSum.TernaryCoverRegularity.swapEdge_swapEdge

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryCoverRegularity
open Finset TernaryJointType TernaryCoverLocal
variable {L : ℕ}
namespace ThreeSum.TernaryCoverRegularity
theorem _root_.solution (α π : DigitType) :
    Function.Injective (swapEdge (α := α) (π := π) (L := L)) :=
  Function.LeftInverse.injective (fun e => swapEdge_swapEdge e)
end ThreeSum.TernaryCoverRegularity
