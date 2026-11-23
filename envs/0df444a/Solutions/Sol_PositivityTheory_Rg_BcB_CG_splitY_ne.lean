-- Prove2me | solution 1 for PositivityTheory.Rg.BcB.CG.splitY_ne
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:13:18.04293+00:00
-- url     : https://prove2.me/submissions/0ee47087-f0a1-45cc-b620-88e264b6fa3a

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
namespace PositivityTheory.Rg.BcB.CG
theorem _root_.solution (w : ι) (t : X) (z : {v // v ≠ w} → X) (v : {v // v ≠ w}) : splitY w t z v = z v := by
  simp [splitY, v.2]
end PositivityTheory.Rg.BcB.CG
