-- Prove2me | solution 1 for QuantumInfo.IsCodeProjector.posSemidef
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T23:49:22.562089+00:00
-- url     : https://prove2.me/submissions/0722b647-0aa1-4908-be57-490c36c1deb6

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
namespace QuantumInfo.IsCodeProjector
theorem _root_.solution : P.PosSemidef := by
  have h : P = Pᴴ * P := by rw [hP.conjTranspose_eq, hP.mul_self]
  rw [h]
  exact posSemidef_conjTranspose_mul_self P
end QuantumInfo.IsCodeProjector
