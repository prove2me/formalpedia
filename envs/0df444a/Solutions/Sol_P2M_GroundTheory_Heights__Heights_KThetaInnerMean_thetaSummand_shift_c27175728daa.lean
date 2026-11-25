-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_KThetaInnerMean_thetaSummand_shift_c27175728daa
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T04:01:21.321121+00:00
-- url     : https://prove2.me/submissions/3e842385-0444-48c1-bac8-b91c72fe9bd8

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsTheta
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_ThetaGauss
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PThetaInnerMean

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open Matrix Real MeasureTheory
noncomputable section
open GroundTheory.Heights₂.Heights.KThetaInnerMean
namespace GroundTheory.Heights₂.Heights.KThetaInnerMean
theorem _root_.solution {g : ℕ} (X Y : Matrix (Fin g) (Fin g) ℝ) (a b u₁ u₂ : Fin g → ℝ)
    (k : Fin g → ℤ) :
    thetaSummand X Y a b (periodMatrix X Y *ᵥ (fun i => (u₁ i : ℂ)) + fun i => (u₂ i : ℂ)) k =
      Complex.exp (((2 * π * ∑ i, a i * u₂ i : ℝ) : ℂ) * Complex.I) *
        (thetaSummand X Y a b
            (periodMatrix X Y *ᵥ (fun i => (u₁ i : ℂ)) + fun i => ((0 : Fin g → ℝ) i : ℂ)) k *
          torusChar k u₂) := by
  unfold thetaSummand torusChar
  rw [← Complex.exp_add, ← Complex.exp_add]
  congr 1
  simp only [dotProduct, Pi.add_apply, Pi.zero_apply, intVec, Complex.ofReal_zero, add_zero,
    mul_add, add_mul, Finset.sum_add_distrib, Complex.ofReal_add, Complex.ofReal_intCast,
    Complex.ofReal_mul, Complex.ofReal_sum, Complex.ofReal_ofNat]
  ring
end GroundTheory.Heights₂.Heights.KThetaInnerMean
