-- Prove2me | solution 1 for ResidualGaloisRep.isEquiv_of_isAbsolutelyIrreducible_of_charpoly_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/945b1ea9-dcb7-5cb0-8fc9-7d029d8c2852

import Theorems.Thm_ResidualGaloisRep_isEquiv_of_isAbsolutelyIrreducible_of_trace_eq
import Definitions.Def_GaloisRep_ResidualEquiv
import Mathlib.LinearAlgebra.Charpoly.ToMatrix
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Algebra.Algebra.Rat
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ResidualGaloisRep_isEquiv_of_isAbsolutelyIrreducible_of_charpoly_eq

open Module LinearMap

namespace C6P1Cp

theorem trace_eq_of_charpoly_eq {k : Type} [Field k] {V₁ V₂ : Type} [AddCommGroup V₁] [Module k V₁]
    [FiniteDimensional k V₁] [AddCommGroup V₂] [Module k V₂] [FiniteDimensional k V₂]
    (h₁ : Module.finrank k V₁ = 2) (h₂ : Module.finrank k V₂ = 2)
    (f : Module.End k V₁) (g : Module.End k V₂) (hcp : f.charpoly = g.charpoly) : trace k V₁ f = trace k V₂ g := by
  let b₁ := Module.finBasisOfFinrankEq k V₁ h₁
  let b₂ := Module.finBasisOfFinrankEq k V₂ h₂
  rw [LinearMap.trace_eq_matrix_trace k b₁ f, LinearMap.trace_eq_matrix_trace k b₂ g,
    Matrix.trace_eq_neg_charpoly_coeff, Matrix.trace_eq_neg_charpoly_coeff,
    LinearMap.charpoly_toMatrix, LinearMap.charpoly_toMatrix, hcp]

end C6P1Cp

theorem solution
    {k : Type} [Field k] (ρ₁ ρ₂ : ResidualGaloisRep k)
    (h₁ : ρ₁.IsAbsolutelyIrreducible) (h₂ : ρ₂.IsAbsolutelyIrreducible)
    (hcp : ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ,
      (ρ₁.ρ σ).charpoly = (ρ₂.ρ σ).charpoly) :
    ρ₁.IsEquiv ρ₂ :=
  ResidualGaloisRep.isEquiv_of_isAbsolutelyIrreducible_of_trace_eq ρ₁ ρ₂ h₁ h₂ fun σ =>
    C6P1Cp.trace_eq_of_charpoly_eq ρ₁.finrank_eq ρ₂.finrank_eq _ _ (hcp σ)

end S_ResidualGaloisRep_isEquiv_of_isAbsolutelyIrreducible_of_charpoly_eq
end P2MW
export P2MW.S_ResidualGaloisRep_isEquiv_of_isAbsolutelyIrreducible_of_charpoly_eq (solution)
