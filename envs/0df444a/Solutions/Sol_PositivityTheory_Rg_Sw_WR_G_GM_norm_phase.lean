-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.WR.G.GM.norm_phase
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:03:50.398834+00:00
-- url     : https://prove2.me/submissions/fd14b60b-3837-4715-88e4-702f8713d589

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_GaussS
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_GaussM
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_G_GM_gramX_isHermitian
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_G_GM_trace_im_zero

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
theorem _root_.solution {ε : Fin m → Bool} {t : ℝ} {b : Matrix (Fin n) (Fin n) ℂ} (hb : b.IsHermitian)
    (x : Fin m → Fin n → ℂ) : ‖Complex.exp (Complex.I * t * (b * gramX ε x).trace)‖ = 1 := by
  rw [Complex.norm_exp]
  have h0 := trace_im_zero hb (gramX_isHermitian ε x)
  have : (Complex.I * t * (b * gramX ε x).trace).re = 0 := by
    simp [Complex.mul_re, h0]
  rw [this, Real.exp_zero]
end PositivityTheory.Rg.Sw.WR.G.GM
