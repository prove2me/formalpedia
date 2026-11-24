-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_radialTransform_eq_zero_of_const_e9745533580f
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:55:52.639812+00:00
-- url     : https://prove2.me/submissions/9aeafcf6-6676-4fc2-a2d0-20b36a12ccb8

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StRegLelongAnnulus
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StRegRadialWeight
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_integral_const_mul_dpow_df0a3ef03557

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
open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets
open scoped ContDiff
noncomputable section
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution (e : ℕ) (a : ℝ → ℝ) {t₀ t : ℝ}
    (ha : ∀ τ ∈ Set.Icc 0 t₀, a τ = a 0) (ht : t ∈ Set.Icc 0 t₀) :
    radialTransform (e + 1) a t = 0 := by
  have hint : ∫ τ in (0 : ℝ)..t, a τ * (((e + 1 : ℕ) : ℝ) * τ ^ (e + 1 - 1)) =
      ∫ τ in (0 : ℝ)..t, a 0 * (((e + 1 : ℕ) : ℝ) * τ ^ (e + 1 - 1)) := by
    refine intervalIntegral.integral_congr fun τ hτ => ?_
    rw [Set.uIcc_of_le ht.1] at hτ
    rw [ha τ ⟨hτ.1, hτ.2.trans ht.2⟩]
  rw [radialTransform, hint, integral_const_mul_dpow, ha t ht]
  ring
end GroundTheory.Heights₂.Heights
