-- Prove2me | solution 1 for ZetaZeros.D.EllReg.one_add_pow_mul_norm_fourier_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T16:27:34.864144+00:00
-- url     : https://prove2.me/submissions/8977379c-a6d5-48b6-b559-a2a09f70aee4

import Definitions.Def_Formalism_UnipotentAdelicQuotients_EllRegCut
import Definitions.Def_Formalism_UnipotentAdelicQuotients_EllipticRegularity_KernDecay
import Theorems.Thm_ZetaZeros_D_EllReg_pow_mul_norm_fourier_le
import Theorems.Thm_ZetaZeros_D_EllReg_one_add_pow_le

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
theorem _root_.solution {f : V → ℂ} (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f)
    (n : ℕ) (w : V) :
    (1 + ‖w‖) ^ n * ‖𝓕 f w‖ ≤ 2 ^ n * (1 + 2 ^ n) * derivL1Norm f n := by
  have hL := pow_mul_norm_fourier_le hf hfc n w
  have h0 := pow_mul_norm_fourier_le hf hfc 0 w
  simp only [pow_zero, one_mul] at h0
  have hmono : derivL1Norm f 0 ≤ derivL1Norm f n :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega))
      (fun _ _ _ => integral_nonneg fun _ => norm_nonneg _)
  have hpos : 0 ≤ ‖𝓕 f w‖ := norm_nonneg _
  have h2 : (0 : ℝ) ≤ 2 ^ n := by positivity
  have hb := one_add_pow_le ‖w‖ (norm_nonneg w) n
  calc (1 + ‖w‖) ^ n * ‖𝓕 f w‖ ≤ 2 ^ n * (1 + ‖w‖ ^ n) * ‖𝓕 f w‖ := mul_le_mul_of_nonneg_right hb hpos
    _ = 2 ^ n * (‖𝓕 f w‖ + ‖w‖ ^ n * ‖𝓕 f w‖) := by ring
    _ ≤ 2 ^ n * (derivL1Norm f n + 2 ^ n * derivL1Norm f n) := by
        refine mul_le_mul_of_nonneg_left ?_ h2
        linarith
    _ = 2 ^ n * (1 + 2 ^ n) * derivL1Norm f n := by ring
end ZetaZeros.D.EllReg
