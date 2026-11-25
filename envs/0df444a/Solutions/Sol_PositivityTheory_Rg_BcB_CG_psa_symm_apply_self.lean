-- Prove2me | solution 1 for PositivityTheory.Rg.BcB.CG.psa_symm_apply_self
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T11:32:37.762666+00:00
-- url     : https://prove2.me/submissions/f390ada6-b91f-4c4d-ae6f-b86199b3c75f

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_ArchimedeanBaseChangeProof_HeckeFubiniCompatibility_PActPi

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
theorem _root_.solution (w : ι) (J : ∀ v, Idx v) : (Equiv.piSplitAt w Idx).symm (J w, fun v : {v // v ≠ w} => J v) = J :=
  (Equiv.piSplitAt w Idx).symm_apply_apply J
end PositivityTheory.Rg.BcB.CG
