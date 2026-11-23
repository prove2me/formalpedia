-- Prove2me | solution 1 for PositivityTheory.Rg.BcB.CG.psa_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:13:14.70634+00:00
-- url     : https://prove2.me/submissions/1648c3a1-eefe-4f72-aec5-2f9017d7ca60

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
theorem _root_.solution (w : ι) (J : ∀ v, Idx v) : Equiv.piSplitAt w Idx J = (J w, fun v : {v // v ≠ w} => J v) := rfl
end PositivityTheory.Rg.BcB.CG
