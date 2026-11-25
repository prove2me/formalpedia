-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.WR.B.Am_line
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T11:52:55.047092+00:00
-- url     : https://prove2.me/submissions/7d21c095-d692-4376-99c6-2439f2a7beb9

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
    Am s (y + t • h) = Am s y + (t : ℂ) • (-((Complex.I * s) • herm h)) := by
  ext i j
  simp only [Am, herm_add, herm_smul, Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.neg_apply,
    smul_eq_mul]
  ring
end PositivityTheory.Rg.Sw.WR.B
