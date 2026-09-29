-- Prove2me | solution 1 for Subalgebra.ringKrullDim_localization_tensor_eq_one_of_irreducible
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/6140dd38-3d24-599d-af33-7b1ce4a3bfeb

import Mathlib
import Theorems.Thm_IsIntegrallyClosed_ringKrullDim_localization_tensor_eq_one_of_irreducible
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Subalgebra_ringKrullDim_localization_tensor_eq_one_of_irreducible

open scoped TensorProduct Polynomial

universe u v

namespace Subalgebra p2m_export "Subalgebra" "inclusion inclusion_injective toAlgebra" end Subalgebra
namespace Subalgebra
p2m_open_scoped "Subalgebra" in

private theorem _root_.Subalgebra.ringKrullDim_localization_tensor_eq_one_of_irreducible
    {Λ K : Type u} [CommRing Λ] [IsDomain Λ] [IsPrincipalIdealRing Λ] {p : Λ} (hp : Irreducible p)
    [Field K] [Algebra Λ K] (R A : Subalgebra Λ K) (e : Λ[X] ≃ₐ[Λ] R) (hRA : R ≤ A)
    (hint : ∀ a : A, IsIntegral R (a : K))
    (hFT : Algebra.FiniteType Λ A) (hIC : IsIntegrallyClosed A)
    (k : Type v) [Field k] [Algebra Λ k] (hk : algebraMap Λ k p = 0)
    (m : Ideal (k ⊗[Λ] A)) [m.IsMaximal] :
    ringKrullDim (Localization.AtPrime m) = 1 := by
  letI : Algebra R A := (Subalgebra.inclusion hRA).toRingHom.toAlgebra
  haveI : IsScalarTower R A K := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : Algebra.IsIntegral R A := ⟨fun a =>
    (isIntegral_algHom_iff (IsScalarTower.toAlgHom R A K) Subtype.val_injective).mp (hint a)⟩
  letI : Algebra Λ[X] R := (e : Λ[X] →+* R).toAlgebra
  letI : Algebra Λ[X] A := ((algebraMap R A).comp (e : Λ[X] →+* R)).toAlgebra
  haveI : IsScalarTower Λ[X] R A := IsScalarTower.of_algebraMap_eq' rfl
  haveI : IsScalarTower Λ Λ[X] A := IsScalarTower.of_algebraMap_eq fun a => by
    show algebraMap Λ A a = algebraMap R A (e (algebraMap Λ Λ[X] a))
    rw [e.commutes]
    rfl
  haveI : Algebra.IsIntegral Λ[X] R :=
    Algebra.isIntegral_of_surjective (show Function.Surjective (e : Λ[X] →+* R) from e.surjective)
  haveI : Algebra.IsIntegral Λ[X] A := Algebra.IsIntegral.trans R
  haveI : Algebra.FiniteType Λ A := hFT
  haveI : Algebra.FiniteType Λ[X] A := Algebra.FiniteType.of_restrictScalars_finiteType Λ Λ[X] A
  haveI : Module.Finite Λ[X] A := Algebra.IsIntegral.finite
  haveI : FaithfulSMul Λ[X] A := by
    rw [faithfulSMul_iff_algebraMap_injective]
    exact (Subalgebra.inclusion_injective hRA).comp e.injective
  haveI : IsIntegrallyClosed A := hIC
  haveI : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing Λ A
  exact IsIntegrallyClosed.ringKrullDim_localization_tensor_eq_one_of_irreducible hp k hk m

end Subalgebra
p2m_export "" "Subalgebra.ringKrullDim_localization_tensor_eq_one_of_irreducible"
theorem solution
    {Λ K : Type u} [CommRing Λ] [IsDomain Λ] [IsPrincipalIdealRing Λ] {p : Λ} (hp : Irreducible p)
    [Field K] [Algebra Λ K] (R A : Subalgebra Λ K) (e : Λ[X] ≃ₐ[Λ] R) (hRA : R ≤ A)
    (hint : ∀ a : A, IsIntegral R (a : K))
    (hFT : Algebra.FiniteType Λ A) (hIC : IsIntegrallyClosed A)
    (k : Type v) [Field k] [Algebra Λ k] (hk : algebraMap Λ k p = 0)
    (m : Ideal (k ⊗[Λ] A)) [m.IsMaximal] :
    ringKrullDim (Localization.AtPrime m) = 1 :=
  Subalgebra.ringKrullDim_localization_tensor_eq_one_of_irreducible hp R A e hRA hint hFT hIC k hk m

end S_Subalgebra_ringKrullDim_localization_tensor_eq_one_of_irreducible
end P2MW
export P2MW.S_Subalgebra_ringKrullDim_localization_tensor_eq_one_of_irreducible (solution)
