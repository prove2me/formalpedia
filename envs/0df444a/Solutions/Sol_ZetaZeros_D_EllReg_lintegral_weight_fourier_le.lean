-- Prove2me | solution 1 for ZetaZeros.D.EllReg.lintegral_weight_fourier_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T16:50:53.31242+00:00
-- url     : https://prove2.me/submissions/72700f17-0e7c-4556-8c56-0aba047668c0

import Definitions.Def_Formalism_UnipotentAdelicQuotients_EllRegCut
import Definitions.Def_Formalism_UnipotentAdelicQuotients_EllipticRegularity_KernDecay
import Theorems.Thm_ZetaZeros_D_EllReg_derivL1Norm_nonneg
import Theorems.Thm_ZetaZeros_D_EllReg_norm_fourier_le_rpow

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
    (∫⁻ w, ENNReal.ofReal ((1 + ‖w‖) ^ m) * ‖𝓕 f w‖ₑ) ≤
      ENNReal.ofReal (2 ^ (m + (Module.finrank ℝ V + 1)) * (1 + 2 ^ (m + (Module.finrank ℝ V + 1))) *
        derivL1Norm f (m + (Module.finrank ℝ V + 1))) *
      ∫⁻ w : V, ENNReal.ofReal ((1 + ‖w‖) ^ (-((Module.finrank ℝ V + 1 : ℕ) : ℝ))) := by
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_mono fun w => ?_
  dsimp only
  have hp : 0 < 1 + ‖w‖ := by positivity
  have h6 := norm_fourier_le_rpow hf hfc (m + (Module.finrank ℝ V + 1)) w
  have hA : 0 ≤ (1 + ‖w‖) ^ m := by positivity
  have hC : 0 ≤ 2 ^ (m + (Module.finrank ℝ V + 1)) * (1 + 2 ^ (m + (Module.finrank ℝ V + 1))) *
      derivL1Norm f (m + (Module.finrank ℝ V + 1)) :=
    mul_nonneg (by positivity) (derivL1Norm_nonneg f _)
  have hexp : (1 + ‖w‖) ^ m * (1 + ‖w‖) ^ (-((m + (Module.finrank ℝ V + 1) : ℕ) : ℝ)) =
      (1 + ‖w‖) ^ (-((Module.finrank ℝ V + 1 : ℕ) : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_add hp]
    congr 1
    push_cast
    ring
  rw [← ofReal_norm, ← ENNReal.ofReal_mul hA, ← ENNReal.ofReal_mul hC]
  apply ENNReal.ofReal_le_ofReal
  calc (1 + ‖w‖) ^ m * ‖𝓕 f w‖
      ≤ (1 + ‖w‖) ^ m * (2 ^ (m + (Module.finrank ℝ V + 1)) * (1 + 2 ^ (m + (Module.finrank ℝ V + 1))) *
        derivL1Norm f (m + (Module.finrank ℝ V + 1)) *
        (1 + ‖w‖) ^ (-((m + (Module.finrank ℝ V + 1) : ℕ) : ℝ))) := mul_le_mul_of_nonneg_left h6 hA
    _ = 2 ^ (m + (Module.finrank ℝ V + 1)) * (1 + 2 ^ (m + (Module.finrank ℝ V + 1))) *
        derivL1Norm f (m + (Module.finrank ℝ V + 1)) *
        ((1 + ‖w‖) ^ m * (1 + ‖w‖) ^ (-((m + (Module.finrank ℝ V + 1) : ℕ) : ℝ))) := by ring
    _ = _ := by rw [hexp]
end ZetaZeros.D.EllReg
