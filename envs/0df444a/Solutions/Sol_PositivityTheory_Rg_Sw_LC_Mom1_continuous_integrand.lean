-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LC.Mom1.continuous_integrand
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T11:44:15.09465+00:00
-- url     : https://prove2.me/submissions/0d432bb0-8dc7-4855-a781-f40a8f84cb6b

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
theorem _root_.solution (c : ℝ) (p q : ℕ) :
    Continuous (fun z : ℂ => z ^ p * star z ^ q * Complex.exp ((-(c * ‖z‖ ^ 2) : ℝ))) :=
  ((continuous_pow p).mul (continuous_star.pow q)).mul
    (Complex.continuous_exp.comp (Complex.continuous_ofReal.comp
      ((continuous_const.mul (continuous_norm.pow 2)).neg)))
end PositivityTheory.Rg.Sw.LC.Mom1
