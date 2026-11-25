-- Prove2me | solution 1 for ReciprocityTheory.PTheta.sphereQuadraticPositivity.quad_lower
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T15:56:45.851045+00:00
-- url     : https://prove2.me/submissions/8189062b-17ed-496f-9abd-56f4a348d95c

import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_ThetaQuasiPeriodStatement
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_NormInvSmulMemSphere
import Theorems.Thm_ReciprocityTheory_PTheta_sphereQuadraticPositivity_quad_smul
import Theorems.Thm_ReciprocityTheory_PTheta_sphereQuadraticPositivity_norm_inv_smul_mem_sphere
import Theorems.Thm_ReciprocityTheory_PTheta_sphereQuadraticPositivity_sum_sq_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Complex Matrix
open ReciprocityTheory ReciprocityTheory.PTheta ReciprocityTheory.PTheta.sphereQuadraticPositivity
variable {ι : Type*} [Fintype ι]
namespace ReciprocityTheory.PTheta.sphereQuadraticPositivity
theorem _root_.solution {X : Type*} [TopologicalSpace X] (Mf : X → Matrix ι ι ℝ) (hc : Continuous Mf)
    (K : Set X) (hK : IsCompact K) (hpos : ∀ p ∈ K, (Mf p).PosDef) :
    ∃ c > 0, ∀ p ∈ K, ∀ x : ι → ℝ, c * ∑ i, x i ^ 2 ≤ x ⬝ᵥ (Mf p *ᵥ x) := by
  classical
  have hF : Continuous (fun q : X × (ι → ℝ) => q.2 ⬝ᵥ (Mf q.1 *ᵥ q.2)) := by
    fun_prop
  have hKS : IsCompact (K ×ˢ Metric.sphere (0 : ι → ℝ) 1) := hK.prod (isCompact_sphere 0 1)
  rcases (K ×ˢ Metric.sphere (0 : ι → ℝ) 1).eq_empty_or_nonempty with he | hne
  · refine ⟨1, one_pos, fun p hp x => ?_⟩
    by_cases hx : x = 0
    · simp [hx]
    · exfalso
      have hy : (p, ‖x‖⁻¹ • x) ∈ K ×ˢ Metric.sphere (0 : ι → ℝ) 1 :=
        ⟨hp, norm_inv_smul_mem_sphere hx⟩
      rw [he] at hy
      exact hy
  · obtain ⟨q0, hq0, hmin⟩ := hKS.exists_isMinOn hne hF.continuousOn
    have hq0S : q0.2 ∈ Metric.sphere (0 : ι → ℝ) 1 := hq0.2
    have hne0 : q0.2 ≠ 0 := by
      intro h
      rw [h] at hq0S
      simp at hq0S
    have hmpos : 0 < q0.2 ⬝ᵥ (Mf q0.1 *ᵥ q0.2) := by
      have h0 := (Matrix.posDef_iff_dotProduct_mulVec.mp (hpos q0.1 hq0.1)).2 hne0
      simpa using h0
    refine ⟨q0.2 ⬝ᵥ (Mf q0.1 *ᵥ q0.2) / (Fintype.card ι + 1), by positivity, fun p hp x => ?_⟩
    by_cases hx : x = 0
    · simp [hx]
    · have hy : (p, ‖x‖⁻¹ • x) ∈ K ×ˢ Metric.sphere (0 : ι → ℝ) 1 :=
        ⟨hp, norm_inv_smul_mem_sphere hx⟩
      have h1 : q0.2 ⬝ᵥ (Mf q0.1 *ᵥ q0.2) ≤ (‖x‖⁻¹ • x) ⬝ᵥ (Mf p *ᵥ (‖x‖⁻¹ • x)) :=
        isMinOn_iff.mp hmin _ hy
      rw [quad_smul] at h1
      have hn : 0 < ‖x‖ := norm_pos_iff.mpr hx
      have h3 : ‖x‖⁻¹ ^ 2 * ‖x‖ ^ 2 = 1 := by field_simp
      have h2 : q0.2 ⬝ᵥ (Mf q0.1 *ᵥ q0.2) * ‖x‖ ^ 2 ≤ x ⬝ᵥ (Mf p *ᵥ x) := by
        calc q0.2 ⬝ᵥ (Mf q0.1 *ᵥ q0.2) * ‖x‖ ^ 2
            ≤ (‖x‖⁻¹ ^ 2 * (x ⬝ᵥ (Mf p *ᵥ x))) * ‖x‖ ^ 2 :=
              mul_le_mul_of_nonneg_right h1 (by positivity)
          _ = x ⬝ᵥ (Mf p *ᵥ x) := by
              rw [mul_comm, ← mul_assoc, mul_comm (‖x‖ ^ 2), h3, one_mul]
      have h4 := sum_sq_le x
      have hc1 : (0:ℝ) < Fintype.card ι + 1 := by positivity
      calc q0.2 ⬝ᵥ (Mf q0.1 *ᵥ q0.2) / (Fintype.card ι + 1) * ∑ i, x i ^ 2
          ≤ q0.2 ⬝ᵥ (Mf q0.1 *ᵥ q0.2) / (Fintype.card ι + 1) * ((Fintype.card ι) * ‖x‖ ^ 2) :=
            mul_le_mul_of_nonneg_left h4 (by positivity)
        _ ≤ q0.2 ⬝ᵥ (Mf q0.1 *ᵥ q0.2) * ‖x‖ ^ 2 := by
          rw [div_mul_eq_mul_div, div_le_iff₀ hc1]
          nlinarith [mul_nonneg hmpos.le (sq_nonneg ‖x‖)]
        _ ≤ _ := h2
end ReciprocityTheory.PTheta.sphereQuadraticPositivity
