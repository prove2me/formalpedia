-- Prove2me | solution 1 for PositivityTheory.Rg.BcB.E2.P.rowsex
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T05:22:12.662749+00:00
-- url     : https://prove2.me/submissions/3a8706d7-339f-4335-ba67-959fbd97d9b1

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_ArchimedeanBaseChangeProof_EigenvalueSeparation_AlmostEverywhereEigen_OneStepOf
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_ArchimedeanBaseChangeProof_EigenvalueSeparation_AlmostEverywhereEigen_PositiveMeasureNorms_Rowsex

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PositivityTheory.Rg.BcB.E1 PositivityTheory.Rg.BcB.E2
open MeasureTheory
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E2 PositivityTheory.Rg.BcB.E2.P
namespace PositivityTheory.Rg.BcB.E2.P
theorem _root_.solution : KerBasic → VecEx → VecNorm → VecInner → RowsEx := by
  intro hK hE hN hI X ι _ Φ T hΦ hT
  have hΨ : ∀ i j, Tst ((fun i j => adj (Φ j i)) i j : X.G → ℂ) := fun i j => (hK X (Φ j i) (hΦ j i)).2.2.2.1
  obtain ⟨k', hc, hv⟩ := hE X ι (fun i j => adj (Φ j i)) hΨ
  obtain ⟨C, Ω, hC, hΩ, hb⟩ := hN X ι (fun i j => adj (Φ j i)) hΨ
  refine ⟨fun i x => k' x i, ⟨hc, ?_, ?_, ⟨C, Ω, hC, hΩ, fun i x => hb x i _ (hv x i)⟩⟩⟩
  · intro i γ hγ x
    refine PiLp.ext fun l => Lp.ext ?_
    filter_upwards [hv (γ * x) i l, hv x i l] with z h1 h2
    rw [h1, h2]
    exact ((hK X _ (hΨ l i)).2.2.1 γ hγ z x).2
  · intro u i
    filter_upwards [hT u i] with x hx
    rw [hx]
    exact ((hI X ι Φ x i (k' x i) u hΦ).2 (hv x i)).symm
end PositivityTheory.Rg.BcB.E2.P
