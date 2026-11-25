-- Prove2me | solution 1 for ZetaZeros.D.EllReg.pow_mul_norm_fourier_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T16:10:11.645215+00:00
-- url     : https://prove2.me/submissions/97ff90da-78d7-495d-add3-7f0ce64925be

import Definitions.Def_Formalism_UnipotentAdelicQuotients_EllRegCut
import Definitions.Def_Formalism_UnipotentAdelicQuotients_EllipticRegularity_KernDecay
import Theorems.Thm_ZetaZeros_D_EllReg_integrable_iteratedFDeriv

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
    ‖w‖ ^ n * ‖𝓕 f w‖ ≤ 2 ^ n * derivL1Norm f n := by
  have h := Real.pow_mul_norm_iteratedFDeriv_fourier_le (K := 0) (N := n)
    (hf.of_le (by exact_mod_cast le_top))
    (fun k j _ _ => integrable_iteratedFDeriv hf hfc k j) (k := 0) (n := n) (by simp) le_rfl w
  simp only [norm_iteratedFDeriv_zero, pow_zero, one_mul, Nat.cast_zero, mul_zero, zero_add,
    Finset.sum_product, Finset.sum_range_one] at h
  unfold derivL1Norm
  exact h
end ZetaZeros.D.EllReg
