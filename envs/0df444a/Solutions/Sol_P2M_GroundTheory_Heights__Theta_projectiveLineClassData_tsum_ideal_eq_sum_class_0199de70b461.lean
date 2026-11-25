-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Theta_projectiveLineClassData_tsum_ideal_eq_sum_class_0199de70b461
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T08:44:37.309238+00:00
-- url     : https://prove2.me/submissions/2879f963-aaa2-435e-abac-0ae6a437c858

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_EisensteinZeta_MirabolicInduction_DiscrNegAndAbsNormMul
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_EisensteinZeta_DedekindZetaSeries_SummableDedekindZetaTerm
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_EisensteinZeta_MirabolicInduction_DedekindZetaEqSumRealEisenstein

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
variable (K : Type) [Field K] [NumberField K]
namespace GroundTheory.Heights₂.Theta.projectiveLineClassData
theorem _root_.solution {s : ℝ} (hs : 0 < s) :
    ∑' I : Ideal (𝓞 K), ENNReal.ofReal ((Ideal.absNorm I : ℝ) ^ (-s)) =
      ∑ B : ClassGroup (𝓞 K), ∑' I : (ClassGroup.mk0 ⁻¹' {B} : Set (Ideal (𝓞 K))⁰),
        ENNReal.ofReal ((Ideal.absNorm ((I : (Ideal (𝓞 K))⁰) : Ideal (𝓞 K)) : ℝ) ^ (-s)) := by
  classical
  have hsupp : Function.support (fun I : Ideal (𝓞 K) => ENNReal.ofReal ((Ideal.absNorm I : ℝ) ^ (-s)))
      ⊆ ((Ideal (𝓞 K))⁰ : Set (Ideal (𝓞 K))) := by
    intro I hI
    rw [SetLike.mem_coe, mem_nonZeroDivisors_iff_ne_zero]
    rintro rfl
    apply hI
    simp [Ideal.absNorm_bot, Real.zero_rpow (neg_ne_zero.mpr hs.ne')]
  rw [← tsum_subtype_eq_of_support_subset hsupp]
  change ∑' x : (Ideal (𝓞 K))⁰, ENNReal.ofReal ((Ideal.absNorm (x : Ideal (𝓞 K)) : ℝ) ^ (-s)) = _
  rw [← ENNReal.tsum_fiberwise _ (ClassGroup.mk0 : (Ideal (𝓞 K))⁰ → ClassGroup (𝓞 K)), tsum_fintype]
end GroundTheory.Heights₂.Theta.projectiveLineClassData
