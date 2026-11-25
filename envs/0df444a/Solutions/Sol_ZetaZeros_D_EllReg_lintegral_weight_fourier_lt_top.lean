-- Prove2me | solution 1 for ZetaZeros.D.EllReg.lintegral_weight_fourier_lt_top
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T16:57:12.53579+00:00
-- url     : https://prove2.me/submissions/0a2cbb42-9ba7-44cf-bdc7-b6aea419ca98

import Definitions.Def_Formalism_UnipotentAdelicQuotients_EllRegCut
import Definitions.Def_Formalism_UnipotentAdelicQuotients_EllipticRegularity_KernDecay
import Theorems.Thm_ZetaZeros_D_EllReg_lintegral_weight_fourier_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ZetaZeros ZetaZeros.D ZetaZeros.D.EllReg
open MeasureTheory Metric Filter Topology
open scoped ContDiff FourierTransform ENNReal
noncomputable section
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]
namespace ZetaZeros.D.EllReg
theorem _root_.solution {f : V → ℂ} (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f) (m : ℕ) :
    (∫⁻ w, ENNReal.ofReal ((1 + ‖w‖) ^ m) * ‖𝓕 f w‖ₑ) < ⊤ := by
  refine lt_of_le_of_lt (lintegral_weight_fourier_le hf hfc m)
    (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (finite_integral_one_add_norm ?_))
  push_cast
  linarith
end ZetaZeros.D.EllReg
