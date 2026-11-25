-- Prove2me | solution 1 for ZetaZeros.D.EllReg.norm_fourier_le_rpow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T16:41:44.930844+00:00
-- url     : https://prove2.me/submissions/c1dcb7ab-c873-41c7-88c7-4444bf2d83de

import Definitions.Def_Formalism_UnipotentAdelicQuotients_EllRegCut
import Definitions.Def_Formalism_UnipotentAdelicQuotients_EllipticRegularity_KernDecay
import Theorems.Thm_ZetaZeros_D_EllReg_one_add_pow_mul_norm_fourier_le

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
theorem _root_.solution {f : V → ℂ} (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f) (n : ℕ) (w : V) :
    ‖𝓕 f w‖ ≤ 2 ^ n * (1 + 2 ^ n) * derivL1Norm f n * (1 + ‖w‖) ^ (-(n : ℝ)) := by
  have h5 := one_add_pow_mul_norm_fourier_le hf hfc n w
  have hp : 0 < 1 + ‖w‖ := by positivity
  have hpn : 0 < (1 + ‖w‖) ^ n := pow_pos hp n
  rw [Real.rpow_neg hp.le, Real.rpow_natCast, ← div_eq_mul_inv, le_div_iff₀ hpn]
  linarith [h5, mul_comm ((1 + ‖w‖) ^ n) ‖𝓕 f w‖]
end ZetaZeros.D.EllReg
