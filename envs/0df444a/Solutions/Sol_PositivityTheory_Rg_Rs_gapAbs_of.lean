-- Prove2me | solution 1 for PositivityTheory.Rg.Rs.gapAbs_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T05:21:33.931724+00:00
-- url     : https://prove2.me/submissions/55dde143-6973-4d49-9403-955ac99b6e59

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ResidualSpectrum_ExponentialNegativity_GapAbsOf

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Classical
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Rs
namespace PositivityTheory.Rg.Rs
theorem _root_.solution (h1 : GapOp) (h2 : GapPoly) : GapAbs := by
  intro k _ _ n V Γ _ _ _ B red ρ t v S hD hE h0 z hz
  obtain ⟨W, U, Z, a1, a2, a3, a4, a5, a6, a7⟩ := h1 k n V Γ B red ρ t v _ hD hE.2
  exact h2 (Fintype.card k) n Fintype.one_lt_card V B W U Z S hD.pos hE.1 h0 (a4 ▸ hD.ne) a1 a2 a3 a5
    (fun j hj => by rw [a4]; exact a6 j hj) (fun j hj => by rw [a4]; exact a7 j hj) z hz
end PositivityTheory.Rg.Rs
