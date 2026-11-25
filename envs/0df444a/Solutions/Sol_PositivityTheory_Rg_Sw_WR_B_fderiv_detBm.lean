-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.WR.B.fderiv_detBm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:38:48.781027+00:00
-- url     : https://prove2.me/submissions/b3f26573-1f37-4cf7-a53f-09adb2e2650b

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_ClsBoundB
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_ClsBound
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_B_line_hasDerivAt
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_B_det_line
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_B_Bm_line
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_B_contDiff_detBm
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_B_det_Bm_ne
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_B_diffAt_of


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
theorem _root_.solution {s : ℂ} (hs : s = 1 ∨ s = -1) (y h : E n) :
    fderiv ℝ (fun y => (Bm s y).det) y h = (Bm s y).det * ((Bm s y)⁻¹ * ((Complex.I * s) • herm h)).trace := by
  have h1 := line_hasDerivAt (diffAt_of (contDiff_detBm s) y) h
  have h2 := det_line (Bm s y) ((Complex.I * s) • herm h) (det_Bm_ne hs y)
  have e : (fun t : ℝ => (Bm s (y + t • h)).det) = fun t : ℝ => (Bm s y + (t : ℂ) • ((Complex.I * s) • herm h)).det :=
    funext fun t => by rw [Bm_line]
  rw [e] at h1
  exact h1.unique h2
end PositivityTheory.Rg.Sw.WR.B
