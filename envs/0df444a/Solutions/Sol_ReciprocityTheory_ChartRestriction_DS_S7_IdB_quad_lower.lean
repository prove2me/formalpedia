-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.S7.IdB.quad_lower
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:21:30.037333+00:00
-- url     : https://prove2.me/submissions/52de14b4-ac93-4ed3-8318-a52887ead172

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_IdThmB
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_IdB_quad_scale

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open scoped ComplexOrder
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ}
open ReciprocityTheory.ChartRestriction.DS.S7.IdB
namespace ReciprocityTheory.ChartRestriction.DS.S7.IdB
theorem _root_.solution {x : Matrix (Fin n) (Fin n) ℂ} (hx : x.PosDef) :
    ∃ c > 0, ∀ v : Fin n → ℂ, c * ‖v‖ ^ 2 ≤ (star v ⬝ᵥ (x *ᵥ v)).re := by
  have hq : Continuous fun v : Fin n → ℂ => (star v ⬝ᵥ (x *ᵥ v)).re :=
    Complex.continuous_re.comp (continuous_id.star.dotProduct (continuous_const.matrix_mulVec continuous_id))
  have hpos : ∀ v : Fin n → ℂ, v ≠ 0 → 0 < (star v ⬝ᵥ (x *ᵥ v)).re := fun v hv => by
    have h := (Complex.lt_def.mp (hx.dotProduct_mulVec_pos hv)).1
    simpa using h
  have hnorm : ∀ v : Fin n → ℂ, v ≠ 0 → ‖((‖v‖⁻¹ : ℝ) : ℂ) • v‖ = 1 := fun v hv => by
    rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity),
      inv_mul_cancel₀ (norm_ne_zero_iff.mpr hv)]
  have hback : ∀ v : Fin n → ℂ, v ≠ 0 → ((‖v‖ : ℝ) : ℂ) • (((‖v‖⁻¹ : ℝ) : ℂ) • v) = v := fun v hv => by
    rw [smul_smul, ← Complex.ofReal_mul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hv), Complex.ofReal_one,
      one_smul]
  by_cases hS : ∃ u : Fin n → ℂ, ‖u‖ = 1
  · obtain ⟨u, hu⟩ := hS
    have hne : (Metric.sphere (0 : Fin n → ℂ) 1).Nonempty := ⟨u, by simpa using hu⟩
    obtain ⟨u0, hu0, hmin⟩ := (isCompact_sphere (0 : Fin n → ℂ) 1).exists_isMinOn hne hq.continuousOn
    have hu0n : ‖u0‖ = 1 := by simpa using hu0
    have hu00 : u0 ≠ 0 := by
      intro h
      rw [h, norm_zero] at hu0n
      exact zero_ne_one hu0n
    refine ⟨_, hpos u0 hu00, fun v => ?_⟩
    by_cases hv : v = 0
    · subst hv
      simp
    · set u := ((‖v‖⁻¹ : ℝ) : ℂ) • v
      have hum : u ∈ Metric.sphere (0 : Fin n → ℂ) 1 := by
        rw [mem_sphere_zero_iff_norm]
        exact hnorm v hv
      have h1 := hmin hum
      rw [← hback v hv, quad_scale]
      have : ‖((‖v‖ : ℝ) : ℂ) • u‖ = ‖v‖ := by rw [hback v hv]
      rw [this, mul_comm]
      exact mul_le_mul_of_nonneg_left h1 (by positivity)
  · refine ⟨1, one_pos, fun v => ?_⟩
    by_cases hv : v = 0
    · subst hv
      simp
    · exact absurd ⟨_, hnorm v hv⟩ hS
end ReciprocityTheory.ChartRestriction.DS.S7.IdB
