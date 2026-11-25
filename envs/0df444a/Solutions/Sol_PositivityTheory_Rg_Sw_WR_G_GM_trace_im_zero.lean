-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.WR.G.GM.trace_im_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T11:51:28.707146+00:00
-- url     : https://prove2.me/submissions/cf4359b0-0d1d-463a-aa65-e64841a03bc9

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_GaussS
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_GaussM

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
open scoped ComplexOrder
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR PositivityTheory.Rg.Sw.WR.G
open PositivityTheory.Rg.Sw
variable {m n : ℕ}
open PositivityTheory.Rg.Sw.WR.G.GM
namespace PositivityTheory.Rg.Sw.WR.G.GM
theorem _root_.solution {b Q : Matrix (Fin n) (Fin n) ℂ} (hb : b.IsHermitian) (hQ : Q.IsHermitian) :
    (b * Q).trace.im = 0 := by
  have h : star (b * Q).trace = (b * Q).trace := by
    rw [← Matrix.trace_conjTranspose, conjTranspose_mul, hb.eq, hQ.eq, Matrix.trace_mul_comm]
  have := congrArg Complex.im h
  simp only [Complex.star_def, Complex.conj_im] at this
  linarith
end PositivityTheory.Rg.Sw.WR.G.GM
