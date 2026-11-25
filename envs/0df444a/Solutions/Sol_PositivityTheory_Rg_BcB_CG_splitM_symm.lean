-- Prove2me | solution 1 for PositivityTheory.Rg.BcB.CG.splitM_symm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T11:40:42.341474+00:00
-- url     : https://prove2.me/submissions/0b70449a-7986-44bc-8dc8-5e9a336a06ce

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_ArchimedeanBaseChangeProof_HeckeFubiniCompatibility_PActPi
import Theorems.Thm_PositivityTheory_Rg_BcB_CG_splitY_self
import Theorems.Thm_PositivityTheory_Rg_BcB_CG_splitY_ne
import Theorems.Thm_PositivityTheory_Rg_BcB_CG_splitM_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.CG
variable {ι : Type} [DecidableEq ι] {X : Type}
variable {Idx : ι → Type}
namespace PositivityTheory.Rg.BcB.CG
theorem _root_.solution [MeasurableSpace X] (w : ι) (t : X) (z : {v // v ≠ w} → X) :
    (splitM w).symm (t, z) = splitY w t z := by
  rw [MeasurableEquiv.symm_apply_eq, splitM_apply]
  refine Prod.ext (splitY_self w t z).symm ?_
  funext v
  exact (splitY_ne w t z v).symm
end PositivityTheory.Rg.BcB.CG
