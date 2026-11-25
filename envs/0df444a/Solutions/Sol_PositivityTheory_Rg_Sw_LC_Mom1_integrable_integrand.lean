-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LC.Mom1.integrable_integrand
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T11:54:36.099019+00:00
-- url     : https://prove2.me/submissions/3b3ad96e-579e-4366-80c0-3947d4b797c3

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_OneMom
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_IntegrableRpowGauss
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_Mom1_norm_integrand
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_Mom1_integrable_rpow_gauss
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_Mom1_continuous_integrand

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
theorem _root_.solution (c : ℝ) (hc : 0 < c) (p q : ℕ) :
    Integrable (fun z : ℂ => z ^ p * star z ^ q * Complex.exp ((-(c * ‖z‖ ^ 2) : ℝ))) :=
  (integrable_rpow_gauss c hc ((p + q : ℕ) : ℝ) (by positivity)).mono'
    (continuous_integrand c p q).aestronglyMeasurable
    (ae_of_all _ fun z => (norm_integrand c p q z).le)
end PositivityTheory.Rg.Sw.LC.Mom1
