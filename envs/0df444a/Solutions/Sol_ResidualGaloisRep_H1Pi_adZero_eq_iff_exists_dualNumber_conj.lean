-- Prove2me | solution 1 for ResidualGaloisRep.H1Pi_adZero_eq_iff_exists_dualNumber_conj
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/e5ec236b-8f74-578c-b6ee-682793bbcfed

import Mathlib
import Definitions.Def_GaloisRep_AdZero
import Definitions.Def_GroupCohomology_TangentSpace
import Theorems.Thm_groupCohomology_dualLiftToCochain_sub_mem_oneCoboundaries_iff
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ResidualGaloisRep_H1Pi_adZero_eq_iff_exists_dualNumber_conj

set_option autoImplicit false

open IsLocalRing groupCohomology TrivSqZeroExt
open scoped DualNumber

theorem solution
    (k : Type) [Field k] (ρbar : ResidualGaloisRep k) (h2 : IsUnit (2 : k))
    (ρ ρ' : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* (DualNumber (Module.End k ρbar.V))ˣ)
    (hρ : IsDualLift ρbar.ρ.toHomUnits ρ) (hρ' : IsDualLift ρbar.ρ.toHomUnits ρ')
    (c c' : cocycles₁ ρbar.adZero)
    (hc : ∀ σ, ((c : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →
        ↥(LinearMap.ker (LinearMap.trace k ρbar.V))) σ : Module.End k ρbar.V) =
      dualLiftToCochain ρbar.ρ.toHomUnits ρ σ)
    (hc' : ∀ σ, ((c' : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →
        ↥(LinearMap.ker (LinearMap.trace k ρbar.V))) σ : Module.End k ρbar.V) =
      dualLiftToCochain ρbar.ρ.toHomUnits ρ' σ) :
    H1π ρbar.adZero c = H1π ρbar.adZero c' ↔
      ∃ w : (DualNumber (Module.End k ρbar.V))ˣ,
        (w : DualNumber (Module.End k ρbar.V)).fst = 1 ∧ ∀ σ, ρ' σ = w * ρ σ * w⁻¹ := by
  classical
  rw [H1π_eq_iff, ← groupCohomology.dualLiftToCochain_sub_mem_oneCoboundaries_iff (k := k) hρ hρ']

  have hconj : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (m : Module.End k ρbar.V),
      (adjointRep k ρbar.ρ.toHomUnits).ρ σ m = ρbar.ρ σ * m * ρbar.ρ σ⁻¹ := by
    intro σ m
    rw [adjointRep_ρ_apply, ← map_inv]
    rfl
  simp only [coboundaries₁, LinearMap.mem_range]
  constructor
  · rintro ⟨m₀, hm₀⟩
    refine ⟨(m₀ : Module.End k ρbar.V), funext fun σ => ?_⟩
    have h1 := congrArg Subtype.val (congrFun hm₀ σ)
    rw [Pi.sub_apply, Submodule.coe_sub, hc σ, hc' σ, d₀₁_hom_apply, Submodule.coe_sub,
      ResidualGaloisRep.adZero_ρ, ResidualGaloisRep.adZeroRep_apply_coe] at h1
    rw [Pi.sub_apply, ← h1, d₀₁_hom_apply, hconj]
  · rintro ⟨m, hm⟩

    set s : k := (h2.unit⁻¹ : kˣ) * LinearMap.trace k ρbar.V m with hs
    have htr1 : LinearMap.trace k ρbar.V (1 : Module.End k ρbar.V) = 2 := by
      rw [LinearMap.trace_one, ρbar.finrank_eq, Nat.cast_ofNat]
    have hm₀ : m - s • (1 : Module.End k ρbar.V) ∈ LinearMap.ker (LinearMap.trace k ρbar.V) := by
      rw [LinearMap.mem_ker, map_sub, map_smul, htr1, hs, smul_eq_mul, mul_assoc, mul_comm _ (2 : k),
        ← mul_assoc, IsUnit.val_inv_mul, one_mul, sub_self]
    refine ⟨⟨m - s • (1 : Module.End k ρbar.V), hm₀⟩, funext fun σ => Subtype.ext ?_⟩
    have h1 := congrFun hm σ
    rw [Pi.sub_apply, d₀₁_hom_apply, hconj] at h1
    rw [Pi.sub_apply, d₀₁_hom_apply, Submodule.coe_sub, Submodule.coe_sub, hc σ, hc' σ, ← h1,
      ResidualGaloisRep.adZero_ρ, ResidualGaloisRep.adZeroRep_apply_coe]
    simp only [mul_sub, sub_mul, Algebra.mul_smul_comm, Algebra.smul_mul_assoc, mul_one, ← map_mul,
      mul_inv_cancel, map_one]
    abel

end S_ResidualGaloisRep_H1Pi_adZero_eq_iff_exists_dualNumber_conj
end P2MW
export P2MW.S_ResidualGaloisRep_H1Pi_adZero_eq_iff_exists_dualNumber_conj (solution)
