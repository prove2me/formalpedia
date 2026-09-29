-- Prove2me | solution 1 for ResidualGaloisRep.injective_map_H1_of_adZero_le_adRep
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/b3f3a694-288f-5fcc-afec-16292c9abc6c

import Mathlib
import Definitions.Def_GaloisRep_AdZero
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ResidualGaloisRep_injective_map_H1_of_adZero_le_adRep

set_option autoImplicit false

open CategoryTheory groupCohomology

theorem solution
    {k : Type} [Field k] (h2 : (2 : k) ≠ 0) (ρbar : ResidualGaloisRep k)
    {G : Type} [Group G] (f : G →* (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))
    (φ : Rep.res f ρbar.adZero ⟶ Rep.res f (Rep.of ρbar.adRep))
    (hφ : ∀ x : LinearMap.ker (LinearMap.trace k ρbar.V), φ.hom x = (x : Module.End k ρbar.V)) :
    Function.Injective (groupCohomology.map (A := Rep.res f ρbar.adZero) (MonoidHom.id G) φ 1).hom := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨c0, rfl⟩ : ∃ c0 : cocycles₁ (Rep.res f ρbar.adZero), (H1π _).hom c0 = x :=
    H1_induction_on x fun c0 => ⟨c0, rfl⟩
  have hval : ∀ τ, (mapCocycles₁ (MonoidHom.id G) φ c0) τ =
      ((c0 τ : LinearMap.ker (LinearMap.trace k ρbar.V)) : Module.End k ρbar.V) :=
    fun τ => hφ (c0 τ)
  erw [H1π_comp_map_apply] at hx
  rw [H1π_eq_zero_iff] at hx
  obtain ⟨m, hm⟩ := hx

  rw [H1π_eq_zero_iff]
  set t : k := (2 : k)⁻¹ * LinearMap.trace k ρbar.V m with ht
  have hm0 : (m : Module.End k ρbar.V) - t • (1 : Module.End k ρbar.V) ∈
      LinearMap.ker (LinearMap.trace k ρbar.V) := by
    rw [LinearMap.mem_ker, map_sub, map_smul, LinearMap.trace_one, ρbar.finrank_eq, smul_eq_mul]
    simp only [Nat.cast_ofNat, ht]
    field_simp
    ring
  refine ⟨⟨m - t • 1, hm0⟩, funext fun g => ?_⟩
  apply Subtype.ext
  have hmg := congrFun hm g
  rw [d₀₁_hom_apply] at hmg ⊢
  rw [hval] at hmg

  rw [← hmg]
  have h1 : ρbar.adRep (f g) (1 : Module.End k ρbar.V) = 1 := by
    rw [ResidualGaloisRep.adRep_apply, mul_one, ← map_mul, mul_inv_cancel, map_one]
  have hact : (((Rep.res f ρbar.adZero).ρ g ⟨m - t • 1, hm0⟩ :
      LinearMap.ker (LinearMap.trace k ρbar.V)) : Module.End k ρbar.V) =
      ρbar.adRep (f g) (m - t • 1) := rfl
  rw [Submodule.coe_sub, hact, map_sub, map_smul, h1]
  change ρbar.adRep (f g) m - t • 1 - (m - t • 1) = ρbar.adRep (f g) m - m
  abel

end S_ResidualGaloisRep_injective_map_H1_of_adZero_le_adRep
end P2MW
export P2MW.S_ResidualGaloisRep_injective_map_H1_of_adZero_le_adRep (solution)
