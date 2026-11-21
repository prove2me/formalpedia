-- Prove2me | solution 1 for QuantumInfo.Channel.adjoint_add
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T23:47:39.633166+00:00
-- url     : https://prove2.me/submissions/d05744c3-bf66-4bfd-83b4-35893111fad7

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
theorem _root_.solution (Φ : Channel n m ι) (P Q : Matrix m m ℂ) :
    Φ.adjoint (P + Q) = Φ.adjoint P + Φ.adjoint Q := by
  simp only [adjoint, Matrix.mul_add, Matrix.add_mul, Finset.sum_add_distrib]
end QuantumInfo.Channel
