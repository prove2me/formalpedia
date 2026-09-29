-- Prove2me | solution 1 for ResidualGaloisRep.exists_basis_monoidHom_toMatrix_eq_baseChangeAlong
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/705614b3-8321-5e25-ab86-de611ae20f84

import Mathlib
import Definitions.Def_GaloisRep_Residual
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ResidualGaloisRep_exists_basis_monoidHom_toMatrix_eq_baseChangeAlong

set_option autoImplicit false

theorem solution
    {k L : Type} [Field k] [Field L] (ψ : k →+* L) (R : ResidualGaloisRep k) :
    ∃ (b : Module.Basis (Fin 2) L (R.baseChangeAlong ψ).V)
      (ρM : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* GL (Fin 2) L),
      GaloisFactorsThroughFiniteLevel ρM ∧
      (∀ σ, (ρM σ).val = LinearMap.toMatrix b b ((R.baseChangeAlong ψ).ρ σ)) ∧
      (∀ σ, (ρM σ).val.charpoly = (LinearMap.charpoly (R.ρ σ)).map ψ) := by
  classical
  letI : Algebra k L := ψ.toAlgebra
  let b₀ : Module.Basis (Fin 2) k R.V := Module.finBasisOfFinrankEq k R.V R.finrank_eq
  let b : Module.Basis (Fin 2) L (R.baseChangeAlong ψ).V := Algebra.TensorProduct.basis L b₀
  let ρM : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* GL (Fin 2) L :=
    (Units.map ((LinearMap.toMatrixAlgEquiv b).toRingEquiv.toMonoidHom)).comp (R.baseChangeAlong ψ).ρ.toHomUnits
  have hval : ∀ σ, (ρM σ).val = LinearMap.toMatrix b b ((R.baseChangeAlong ψ).ρ σ) := fun σ => rfl
  refine ⟨b, ρM, ?_, hval, fun σ => ?_⟩
  · obtain ⟨L₀, hL₀, h1⟩ := (R.baseChangeAlong ψ).factorsThroughFiniteLevel
    refine ⟨L₀, hL₀, fun σ hσ => ?_⟩
    apply Units.ext
    rw [hval, h1 σ hσ, Units.val_one]
    exact LinearMap.toMatrix_one b
  · rw [hval]
    have hρ : (R.baseChangeAlong ψ).ρ σ = (R.ρ σ).baseChange L := rfl
    rw [hρ]
    show (LinearMap.toMatrix (Algebra.TensorProduct.basis L b₀) (Algebra.TensorProduct.basis L b₀) ((R.ρ σ).baseChange L)).charpoly = _
    rw [LinearMap.toMatrix_baseChange, Matrix.charpoly_map, LinearMap.charpoly_toMatrix]
    rfl

end S_ResidualGaloisRep_exists_basis_monoidHom_toMatrix_eq_baseChangeAlong
end P2MW
export P2MW.S_ResidualGaloisRep_exists_basis_monoidHom_toMatrix_eq_baseChangeAlong (solution)
