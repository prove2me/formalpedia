-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.WR.B.Bm_line
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T11:48:40.621572+00:00
-- url     : https://prove2.me/submissions/84a3b912-eafd-42a0-8f4a-7bfa469dd941

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_ClsBoundB
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_ClsBound

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix MvPolynomial
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR PositivityTheory.Rg.Sw.WR.B
open PositivityTheory.Rg.Sw
variable {n : ℕ}
namespace PositivityTheory.Rg.Sw.WR.B
theorem _root_.solution (s : ℂ) (y h : E n) (t : ℝ) :
    Bm s (y + t • h) = Bm s y + (t : ℂ) • ((Complex.I * s) • herm h) := by
  ext i j
  simp only [Bm, herm_add, herm_smul, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  ring
end PositivityTheory.Rg.Sw.WR.B
