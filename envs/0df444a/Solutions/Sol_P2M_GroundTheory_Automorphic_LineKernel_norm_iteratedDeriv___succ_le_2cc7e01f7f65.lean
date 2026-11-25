-- Prove2me | solution 1 for P2M_GroundTheory_Automorphic_LineKernel_norm_iteratedDeriv___succ_le_2cc7e01f7f65
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T03:11:29.519185+00:00
-- url     : https://prove2.me/submissions/28d81405-95de-45ab-a34f-2aba1956f140

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_DixmierMalliavinLineStage
import Definitions.Def_GroundTheory_AutomorphicForms_DixmierMalliavinLineBounds
import Theorems.Thm_GroundTheory_Automorphic_LineKernel_iteratedDeriv_eq_of_deriv
import Theorems.Thm_GroundTheory_Automorphic_LineKernel_convolution_mul_eq_real
import Theorems.Thm_GroundTheory_Automorphic_LineKernel_iteratedDeriv_convolution
import Theorems.Thm_GroundTheory_Automorphic_LineKernel_norm_convolution_le
import Theorems.Thm_GroundTheory_Automorphic_LineKernel_integral_norm_KC_le_one
import Theorems.Thm_P2M_GroundTheory_Automorphic_LineKernel_norm_iteratedDeriv__C_ac13ffdbfcb3
import Theorems.Thm_GroundTheory_Automorphic_LineKernel_coef_nonneg
import Theorems.Thm_GroundTheory_Automorphic_LineKernel_contDiff_iteratedDeriv_of_contDiff
import Theorems.Thm_GroundTheory_Automorphic_LineKernel_hasCompactSupport_iteratedDeriv
import Theorems.Thm_GroundTheory_Automorphic_LineKernel_integrable_KC
import Theorems.Thm_P2M_GroundTheory_Automorphic_LineKernel_contDiff__C_d6b9b6ae5dcf
import Theorems.Thm_P2M_GroundTheory_Automorphic_LineKernel_hasCompactSupport__C_147c0388f3f8


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic
open MeasureTheory Set Filter Topology Real Function ContinuousLinearMap
open scoped ContDiff Convolution Pointwise FourierTransform
set_option linter.unusedSectionVars false
noncomputable section
open GroundTheory.Automorphic.LineKernel
variable {a r : ℕ → ℝ} (ha : ∀ j, 0 < a j) (hr : ∀ j, 0 < r j)
include ha hr
namespace GroundTheory.Automorphic.LineKernel
theorem _root_.solution (n m : ℕ) {B : ℕ → ℝ}
    (hB : ∀ q t, ‖iteratedDeriv q (rem (a (n + 1)) (r (n + 1))) t‖ ≤ B q) (t : ℝ) :
    ‖iteratedDeriv m (ρ a r (n + 1)) t‖ ≤
      ∑ p ∈ Finset.range (n + 2), coef a (n + 1) p * B (p + m) := by
  have hKi := (integrable_KC ha hr n).locallyIntegrable
  have hηc := contDiff_ηC a r (n + 1)
  have hηs := hasCompactSupport_ηC ha hr (n + 1)
  set Φ : ℕ → ℝ → ℂ := fun m u => ∑ p ∈ Finset.range (n + 2),
    (coef a (n + 1) p : ℂ) * (KC a r n ⋆[mul ℂ ℂ] iteratedDeriv (p + m) (ηC a r (n + 1))) u
    with hΦ
  have h0 : ρ a r (n + 1) = Φ 0 := by
    funext u
    simp only [ρ, hΦ, add_zero, iteratedDeriv_convolution hKi hηc hηs]
  have hd : ∀ m, deriv (Φ m) = Φ (m + 1) := by
    intro m; funext x
    have hsum := HasDerivAt.sum (u := Finset.range (n + 2))
      (A := fun p u => (coef a (n + 1) p : ℂ) *
        (KC a r n ⋆[mul ℂ ℂ] iteratedDeriv (p + m) (ηC a r (n + 1))) u)
      (A' := fun p => (coef a (n + 1) p : ℂ) *
        (KC a r n ⋆[mul ℂ ℂ] iteratedDeriv (p + m + 1) (ηC a r (n + 1))) x) (x := x)
      (fun p _ => by
        refine HasDerivAt.const_mul _ ?_
        rw [convolution_mul_eq_real, convolution_mul_eq_real, iteratedDeriv_succ]
        exact (hasCompactSupport_iteratedDeriv hηs (p + m)).hasDerivAt_convolution_right
          (mul ℝ ℂ) hKi ((contDiff_iteratedDeriv_of_contDiff hηc _).of_le (by simp)) x)
    have e : Φ m = ∑ p ∈ Finset.range (n + 2), fun u => (coef a (n + 1) p : ℂ) *
        (KC a r n ⋆[mul ℂ ℂ] iteratedDeriv (p + m) (ηC a r (n + 1))) u := by
      funext u; simp [hΦ, Finset.sum_apply]
    rw [e, hsum.deriv]
    simp only [hΦ, add_assoc]
  rw [h0, iteratedDeriv_eq_of_deriv hd m]
  simp only [hΦ]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun p _ => ?_)
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (coef_nonneg ha _ _)]
  refine mul_le_mul_of_nonneg_left ?_ (coef_nonneg ha _ _)
  have hB' : ∀ u, ‖iteratedDeriv (p + m) (ηC a r (n + 1)) u‖ ≤ B (p + m) := fun u => by
    rw [norm_iteratedDeriv_ηC ha hr]; exact hB _ _
  refine (norm_convolution_le (integrable_KC ha hr n) hB' t).trans ?_
  have h1 := integral_norm_KC_le_one ha hr n
  have h2 : 0 ≤ B (p + m) := (norm_nonneg _).trans (hB (p + m) 0)
  have h3 : 0 ≤ ∫ t, ‖KC a r n t‖ := integral_nonneg fun t => norm_nonneg _
  nlinarith
end GroundTheory.Automorphic.LineKernel
