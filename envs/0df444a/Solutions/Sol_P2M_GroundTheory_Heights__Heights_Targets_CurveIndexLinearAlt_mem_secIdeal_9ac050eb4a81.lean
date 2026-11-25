-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Targets_CurveIndexLinearAlt_mem_secIdeal_9ac050eb4a81
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T06:13:59.091748+00:00
-- url     : https://prove2.me/submissions/6354adc8-a1d2-45db-b039-52b0aafe5e8e

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StatementsCurveIndexLinear
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StatementsCurveRingFinite
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StatementsCurveClosedPointChart
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StatementsInvertibleIndexMul
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PCurveIndexLinear
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_CurveIndexLinearAlt_cu_ne_zero_a60dcb0d33ce
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_CurveIndexLinearAlt_mem_chartLat_one_d525f1fe8df3

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Targets
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
noncomputable section
open GroundTheory.Heights₂.Heights.Targets.CurveIndexLinearAlt
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]
omit [∀ k, Fintype (ι k)]
namespace GroundTheory.Heights₂.Heights.Targets.CurveIndexLinearAlt
theorem _root_.solution {y : (Σ k, ι k) → Ω} {c : ∀ k, ι k} (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) {a : K → ℤ} {z : Ω} :
    z ∈ secIdeal y c a ↔ ∀ c' : ∀ k, ι k, (∀ k, y ⟨k, c' k⟩ ≠ 0) → z / gen y c a c' ∈ chartRingZ y c' := by
  have hu := cu_ne_zero hc a
  rw [secIdeal, AddSubgroup.mem_map]
  constructor
  · rintro ⟨x, hx, rfl⟩ c' hc'
    have hu' := cu_ne_zero hc' a
    convert mem_chartLat_one.mp hx c' hc' using 1
    simp only [AddMonoidHom.coe_mulLeft, gen]
    field_simp
  · intro h
    refine ⟨z * cu y c a, mem_chartLat_one.mpr fun c' hc' => ?_, ?_⟩
    · have hu' := cu_ne_zero hc' a
      convert h c' hc' using 1
      simp only [gen]
      field_simp
    · show (cu y c a)⁻¹ * (z * cu y c a) = z
      rw [mul_comm z, ← mul_assoc, inv_mul_cancel₀ hu, one_mul]
end GroundTheory.Heights₂.Heights.Targets.CurveIndexLinearAlt
