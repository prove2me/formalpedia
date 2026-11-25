-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.WR.G.trace_im_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T11:58:36.146801+00:00
-- url     : https://prove2.me/submissions/1a1a859f-c043-4309-b049-afae77e6698d

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_GWickA
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_GWickB
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_G_gramX_herm

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
variable {m n : ℕ}
namespace PositivityTheory.Rg.Sw.WR.G
theorem _root_.solution (ε : Fin m → Bool) (b : Matrix (Fin n) (Fin n) ℂ) (hb : b.IsHermitian)
    (x : Fin m → Fin n → ℂ) : (b * gramX ε x).trace.im = 0 := by
  have h : star (b * gramX ε x).trace = (b * gramX ε x).trace := by
    rw [← trace_conjTranspose, conjTranspose_mul, gramX_herm, hb.eq, trace_mul_comm]
  have := congrArg Complex.im h
  simp only [Complex.star_def, Complex.conj_im] at this
  linarith
end PositivityTheory.Rg.Sw.WR.G
