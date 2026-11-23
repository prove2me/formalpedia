-- Prove2me | solution 1 for PositivityTheory.Rg.BcB.CG.psa_symm_self
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:13:15.720654+00:00
-- url     : https://prove2.me/submissions/801120e7-c765-489b-897f-8911bab9c0bc

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
theorem _root_.solution (w : ι) (j : Idx w) (J' : ∀ v : {v // v ≠ w}, Idx v) :
    (Equiv.piSplitAt w Idx).symm (j, J') w = j :=
  congrArg Prod.fst ((Equiv.piSplitAt w Idx).apply_symm_apply (j, J'))
end PositivityTheory.Rg.BcB.CG
