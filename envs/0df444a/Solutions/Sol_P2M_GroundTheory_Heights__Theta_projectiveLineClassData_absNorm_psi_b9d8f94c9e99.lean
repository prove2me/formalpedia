-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Theta_projectiveLineClassData_absNorm_psi_b9d8f94c9e99
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T09:02:57.810427+00:00
-- url     : https://prove2.me/submissions/c523b995-25f4-4310-aee5-651ca5d6d4be

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_EisensteinZeta_MirabolicInduction_DiscrNegAndAbsNormMul
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_EisensteinZeta_DedekindZetaSeries_SummableDedekindZetaTerm
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_EisensteinZeta_MirabolicInduction_DedekindZetaEqSumRealEisenstein
import Theorems.Thm_P2M_GroundTheory_Heights__Theta_projectiveLineClassData_abs_norm_eq_fb529326a8de


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Theta
open GroundTheory.Heights₂.Theta.projectiveLineClassData
open NumberField UpperHalfPlane
open scoped nonZeroDivisors
variable {K : Type} [Field K] [NumberField K]
open FractionalIdeal EtaPeriodLatticeClass
local notation "↑ᶠ" J => ((J : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K)
namespace GroundTheory.Heights₂.Theta.projectiveLineClassData
theorem _root_.solution (hK : Module.finrank ℚ K = 2) (σ : K →+* ℂ) (hσ : ∃ x : K, (σ x).im ≠ 0)
    (J : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (x : Nz J) :
    (Ideal.absNorm ((psi J x : (Ideal (𝓞 K))⁰) : Ideal (𝓞 K)) : ℝ) =
      ‖σ (x : K)‖ ^ 2 / ((FractionalIdeal.absNorm (↑ᶠ J) : ℚ) : ℝ) := by
  have h1 := congrArg FractionalIdeal.absNorm (coe_psi J x)
  rw [coeIdeal_absNorm, map_mul, absNorm_span_singleton] at h1
  have hinv : FractionalIdeal.absNorm (↑ᶠ J⁻¹) = (FractionalIdeal.absNorm (↑ᶠ J))⁻¹ := by
    apply eq_inv_of_mul_eq_one_right
    rw [← map_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, map_one]
  rw [hinv] at h1
  have h2 := congrArg (fun q : ℚ => (q : ℝ)) h1
  simp only [Rat.cast_natCast, Rat.cast_mul, Rat.cast_abs, Rat.cast_inv] at h2
  rw [h2, abs_norm_eq hK σ hσ, div_eq_mul_inv]
end GroundTheory.Heights₂.Theta.projectiveLineClassData
