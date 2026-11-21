-- Prove2me | solution 1 for QuantumInfo.eq_klUnitary_mul_diagonal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T23:48:47.753173+00:00
-- url     : https://prove2.me/submissions/43353693-bd2f-42c0-bf61-958be566960f

module
public import Definitions.Def_KnillLaflammeLean_QuantumInfo_Channel
public import Mathlib.Analysis.Matrix.Spectrum
public import Mathlib.Analysis.Matrix.PosDef
public import Mathlib.LinearAlgebra.Matrix.DotProduct
public import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
public import Definitions.Def_KnillLaflammeLean_QuantumInfo_KnillLaflamme

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
    c = klUnitary hc' * diagonal (RCLike.ofReal ∘ hc'.eigenvalues) * star (klUnitary hc') := by
  have := hc'.spectral_theorem
  rwa [conjStarAlgAut_apply] at this
end QuantumInfo
