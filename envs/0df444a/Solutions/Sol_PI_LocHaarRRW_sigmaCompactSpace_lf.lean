-- Prove2me | solution 1 for PI.LocHaarRRW.sigmaCompactSpace_lf
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T09:51:51.624256+00:00
-- url     : https://prove2.me/submissions/7ceeb026-bda5-431e-bb7d-fba279f75579

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalHaarSubgroup_ExistsHaarOfSubgroup
import Theorems.Thm_PI_LocHaarRRW_isCompact_integer
import Theorems.Thm_PI_LocHaarRRW_inv_mem_integer

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ValuativeRel MeasureTheory Topology Polynomial
open PI PI.LocHaarRRW
variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
namespace PI.LocHaarRRW
theorem _root_.solution : SigmaCompactSpace K := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[K]
  have hϖ0 : (ϖ : K) ≠ 0 := fun h => hϖ.ne_zero (Subtype.ext h)
  refine ⟨⟨fun n => (fun y : K => ((ϖ : K) ^ n)⁻¹ * y) '' (𝒪[K] : Set K),
    fun n => (isCompact_integer K).image (continuous_const.mul continuous_id), ?_⟩⟩
  refine Set.eq_univ_of_forall fun x => ?_
  rw [Set.mem_iUnion]
  by_cases hx : x ∈ 𝒪[K]
  · exact ⟨0, x, hx, by simp⟩
  · have hx0 : x ≠ 0 := by rintro rfl; exact hx (zero_mem _)
    have hxi : x⁻¹ ∈ 𝒪[K] := inv_mem_integer hx
    have hne : (⟨x⁻¹, hxi⟩ : 𝒪[K]) ≠ 0 := by
      intro h
      apply hx0
      have := congrArg (fun z : 𝒪[K] => (z : K)) h
      simpa using this
    obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hne hϖ
    have h1 : x⁻¹ = (u : K) * (ϖ : K) ^ n := by
      have := congrArg (fun z : 𝒪[K] => (z : K)) hu
      simpa using this
    set y : K := (((u⁻¹ : 𝒪[K]ˣ) : 𝒪[K]) : K) with hy
    have h2 : (u : K) * y = 1 := by
      rw [hy]; exact congrArg Subtype.val u.mul_inv
    have hp : ((ϖ : K) ^ n) ≠ 0 := pow_ne_zero _ hϖ0
    refine ⟨n, y, SetLike.coe_mem _, ?_⟩
    show ((ϖ : K) ^ n)⁻¹ * y = x
    have h3 : x⁻¹ * (((ϖ : K) ^ n)⁻¹ * y) = 1 := by
      rw [h1]
      calc (u : K) * (ϖ : K) ^ n * (((ϖ : K) ^ n)⁻¹ * y)
          = ((u : K) * y) * ((ϖ : K) ^ n * ((ϖ : K) ^ n)⁻¹) := by ring
        _ = 1 := by rw [h2, mul_inv_cancel₀ hp, one_mul]
    have h4 := inv_eq_of_mul_eq_one_right h3
    rw [inv_inv] at h4
    exact h4.symm
end PI.LocHaarRRW
