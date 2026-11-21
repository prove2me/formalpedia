-- Prove2me | solution 1 for QuantumInfo.Channel.adjoint_unital
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T23:47:02.647279+00:00
-- url     : https://prove2.me/submissions/c21d8759-f4d1-482d-89e5-4ebdd37f9a9a

module
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.Data.Complex.Basic
public import Mathlib.Analysis.Complex.Order
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Analysis.Matrix.PosDef
public import Definitions.Def_KnillLaflammeLean_QuantumInfo_Channel

set_option autoImplicit false
@[expose] public section
public section
open Matrix
open scoped ComplexOrder
open QuantumInfo
open QuantumInfo.Channel
variable {n m ι : Type*} [Fintype n] [Fintype m] [Fintype ι] [DecidableEq n]
namespace QuantumInfo.Channel
theorem _root_.solution [DecidableEq m] (Φ : Channel n m ι) : Φ.adjoint 1 = 1 := by
  rw [adjoint]
  simp only [Matrix.mul_one]
  exact Φ.tp
end QuantumInfo.Channel
