-- Prove2me | solution 1 for QuantumInfo.star_klUnitary_mul_mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T23:50:05.314746+00:00
-- url     : https://prove2.me/submissions/ec6a2a68-89df-43c2-862c-6a2a5362fa0a

module
public import Definitions.Def_KnillLaflammeLean_QuantumInfo_Channel
public import Mathlib.Analysis.Matrix.Spectrum
public import Mathlib.Analysis.Matrix.PosDef
public import Mathlib.LinearAlgebra.Matrix.DotProduct
public import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
public import Definitions.Def_KnillLaflammeLean_QuantumInfo_KnillLaflamme
public import Theorems.Thm_QuantumInfo_klUnitary_star_mul
public import Theorems.Thm_QuantumInfo_eq_klUnitary_mul_diagonal

set_option autoImplicit false
@[expose] public section
public section
open Matrix Unitary
open scoped ComplexOrder ComplexConjugate
open QuantumInfo
variable {n : Type*} [Fintype n]
variable [DecidableEq n] {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {P : Matrix n n ℂ} {E : ι → Matrix n n ℂ} {c : Matrix ι ι ℂ}
variable (hc' : c.IsHermitian)
namespace QuantumInfo
theorem _root_.solution :
    star (klUnitary hc') * c * klUnitary hc' = diagonal (RCLike.ofReal ∘ hc'.eigenvalues) := by
  calc star (klUnitary hc') * c * klUnitary hc'
      = star (klUnitary hc') * (klUnitary hc' * diagonal (RCLike.ofReal ∘ hc'.eigenvalues)
          * star (klUnitary hc')) * klUnitary hc' := by rw [← eq_klUnitary_mul_diagonal]
    _ = diagonal (RCLike.ofReal ∘ hc'.eigenvalues) := by
        rw [Matrix.mul_assoc, Matrix.mul_assoc, klUnitary_star_mul, Matrix.mul_one,
          ← Matrix.mul_assoc, klUnitary_star_mul, Matrix.one_mul]
end QuantumInfo
