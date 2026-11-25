-- Prove2me | solution 1 for PositivityTheory.Rg.BcB.CG.splitM_mp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T11:32:43.967459+00:00
-- url     : https://prove2.me/submissions/08ccef17-aa6b-418a-813f-46de04baa5ad

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
theorem _root_.solution [MeasurableSpace X] [Fintype ι] (μ : Measure X) [SigmaFinite μ] (w : ι) :
    MeasurePreserving (splitM w) (Measure.pi fun _ : ι => μ) (μ.prod (Measure.pi fun _ : {v // v ≠ w} => μ)) :=
  ((@measurePreserving_piUnique {v // v = w} (Subtype.fintype _) (fun _ => X) _ _ (fun _ => μ)).prod (MeasurePreserving.id _)).comp
    (measurePreserving_piEquivPiSubtypeProd (fun _ : ι => μ) (· = w))
end PositivityTheory.Rg.BcB.CG
