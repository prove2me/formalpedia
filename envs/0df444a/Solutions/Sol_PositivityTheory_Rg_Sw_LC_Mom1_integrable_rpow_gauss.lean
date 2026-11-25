-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LC.Mom1.integrable_rpow_gauss
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T11:45:29.352527+00:00
-- url     : https://prove2.me/submissions/fd2322eb-9915-4ebc-8e7d-dc98c0649ea5

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_OneMom
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_IntegrableRpowGauss

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Set Real
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LC PositivityTheory.Rg.Sw.LC.Mom1
namespace PositivityTheory.Rg.Sw.LC.Mom1
theorem _root_.solution (c : ℝ) (hc : 0 < c) (s : ℝ) (hs : 0 ≤ s) :
    Integrable (fun z : ℂ => ‖z‖ ^ s * Real.exp (-c * ‖z‖ ^ (2 : ℝ))) := by
  by_contra h
  have h1 := Complex.integral_rpow_mul_exp_neg_mul_rpow (p := 2) (q := s) (b := c) (by norm_num)
    (by linarith) hc
  rw [integral_undef h] at h1
  have hG := Real.Gamma_pos_of_pos (s := (s + 2) / 2) (by linarith)
  have : 0 < (2 * π / 2) * c ^ (-(s + 2) / 2) * Real.Gamma ((s + 2) / 2) := by
    have := Real.pi_pos
    positivity
  linarith
end PositivityTheory.Rg.Sw.LC.Mom1
