-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LC.Mom1.norm_integrand
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T11:46:24.98134+00:00
-- url     : https://prove2.me/submissions/728b35e9-a36a-43b7-8b58-1ba70a89ce16

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
theorem _root_.solution (c : ℝ) (p q : ℕ) (z : ℂ) :
    ‖z ^ p * star z ^ q * Complex.exp ((-(c * ‖z‖ ^ 2) : ℝ))‖ =
      ‖z‖ ^ ((p + q : ℕ) : ℝ) * Real.exp (-c * ‖z‖ ^ (2 : ℝ)) := by
  rw [norm_mul, norm_mul, norm_pow, norm_pow, norm_star, Complex.norm_exp_ofReal, Real.rpow_natCast,
    Real.rpow_two, pow_add]
  ring_nf
end PositivityTheory.Rg.Sw.LC.Mom1
