-- Prove2me | solution 1 for Representation.exists_isGalois_level_forall_apply_eq_self
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/b61dfd50-31cb-5e0e-949e-843aaa94d0c2

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Representation_exists_isGalois_level_forall_apply_eq_self

set_option autoImplicit false

universe u

namespace P2mS26U1

theorem exists_isGalois_ge (F : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ F] :
    ∃ F' : IntermediateField ℚ (AlgebraicClosure ℚ),
      FiniteDimensional ℚ F' ∧ IsGalois ℚ F' ∧ F ≤ F' := by
  haveI : Normal ℚ (AlgebraicClosure ℚ) := by
    convert @IsAlgClosure.normal ℚ (AlgebraicClosure ℚ) _ _ (AlgebraicClosure.instAlgebra ℚ) inferInstance
    rfl
  let L : IntermediateField ℚ (AlgebraicClosure ℚ) := IntermediateField.normalClosure ℚ F (AlgebraicClosure ℚ)
  haveI : FiniteDimensional ℚ L := normalClosure.is_finiteDimensional ℚ F (AlgebraicClosure ℚ)
  haveI : Normal ℚ L := normalClosure.normal ℚ F (AlgebraicClosure ℚ)
  haveI : IsGalois ℚ L := ⟨⟩
  exact ⟨L, inferInstance, inferInstance, IntermediateField.le_normalClosure F⟩

end P2mS26U1

theorem solution
    {k G V : Type*} [CommSemiring k] [Monoid G] [AddCommMonoid V] [Module k V] [Module.Finite k V]
    (r : G →* (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) (ρ : Representation k G V)
    (hsm : ∀ m : V, ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
      ∀ s, r s ∈ F.fixingSubgroup → ρ s m = m) :
    ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧ IsGalois ℚ F ∧
      ∀ s, r s ∈ F.fixingSubgroup → ∀ m : V, ρ s m = m := by
  classical
  obtain ⟨n, v, hv⟩ := Module.Finite.exists_fin (R := k) (M := V)
  choose Fi hFi hfix using fun i => hsm (v i)
  haveI := hFi
  haveI : FiniteDimensional ℚ (⨆ i, Fi i : IntermediateField ℚ (AlgebraicClosure ℚ)) :=
    IntermediateField.finiteDimensional_iSup_of_finite
  obtain ⟨F, hF, hG, hle⟩ := P2mS26U1.exists_isGalois_ge (⨆ i, Fi i)
  refine ⟨F, hF, hG, fun s hs => ?_⟩
  have hs₀ : r s ∈ (⨆ i, Fi i).fixingSubgroup := IntermediateField.fixingSubgroup_antitone hle hs
  have key : ∀ i, ρ s (v i) = LinearMap.id (R := k) (v i) := fun i =>
    hfix i s (IntermediateField.fixingSubgroup_antitone (le_iSup Fi i) hs₀)
  have : ρ s = LinearMap.id := LinearMap.ext_on_range hv key
  intro m
  exact LinearMap.congr_fun this m

end S_Representation_exists_isGalois_level_forall_apply_eq_self
end P2MW
export P2MW.S_Representation_exists_isGalois_level_forall_apply_eq_self (solution)
