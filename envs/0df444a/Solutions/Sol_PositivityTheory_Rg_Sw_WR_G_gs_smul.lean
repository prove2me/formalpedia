-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.WR.G.gs_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T11:57:18.835193+00:00
-- url     : https://prove2.me/submissions/8870ed93-bb31-44ff-b178-fd1cd3581ee4

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_NormMono
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_ContinuousGramX

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Matrix MvPolynomial
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR PositivityTheory.Rg.Sw.WR.G
open PositivityTheory.Rg.Sw
namespace PositivityTheory.Rg.Sw.WR.G
theorem _root_.solution {m n : ℕ} (c : ℝ) (ζ : ℂ) (hζ : ‖ζ‖ = 1) (x : Fin m → Fin n → ℂ) : gs c (ζ • x) = gs c x := by
  unfold gs
  simp [hζ]
end PositivityTheory.Rg.Sw.WR.G
