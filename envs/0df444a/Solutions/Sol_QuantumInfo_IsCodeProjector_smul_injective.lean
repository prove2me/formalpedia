-- Prove2me | solution 1 for QuantumInfo.IsCodeProjector.smul_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T23:48:29.277925+00:00
-- url     : https://prove2.me/submissions/e9d11d42-f7cd-4d95-bc7d-07d7428b1298

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
open QuantumInfo.IsCodeProjector
variable {P : Matrix n n ℂ} (hP : IsCodeProjector P)
include hP
omit [Fintype n] hP
namespace QuantumInfo.IsCodeProjector
theorem _root_.solution (hP0 : P ≠ 0) {a b : ℂ} (h : a • P = b • P) : a = b := by
  have h1 : (a - b) • P = 0 := by rw [sub_smul, h, sub_self]
  rcases smul_eq_zero.mp h1 with h2 | h2
  · exact sub_eq_zero.mp h2
  · exact absurd h2 hP0
end QuantumInfo.IsCodeProjector
