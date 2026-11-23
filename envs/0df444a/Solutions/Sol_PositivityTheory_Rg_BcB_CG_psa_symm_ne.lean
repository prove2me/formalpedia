-- Prove2me | solution 1 for PositivityTheory.Rg.BcB.CG.psa_symm_ne
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:02:58.34658+00:00
-- url     : https://prove2.me/submissions/552b131e-0f02-479b-b334-ca885f85f13f

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
theorem _root_.solution (w : ι) (j : Idx w) (J' : ∀ v : {v // v ≠ w}, Idx v) (v : {v // v ≠ w}) :
    (Equiv.piSplitAt w Idx).symm (j, J') v = J' v :=
  congrFun (congrArg Prod.snd ((Equiv.piSplitAt w Idx).apply_symm_apply (j, J'))) v
end PositivityTheory.Rg.BcB.CG
