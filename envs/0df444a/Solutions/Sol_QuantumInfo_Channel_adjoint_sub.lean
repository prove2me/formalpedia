-- Prove2me | solution 1 for QuantumInfo.Channel.adjoint_sub
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T23:47:11.736968+00:00
-- url     : https://prove2.me/submissions/44706606-f6a9-4e56-97ab-741882f8ff45

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
    Φ.adjoint (P - Q) = Φ.adjoint P - Φ.adjoint Q := by
  simp only [adjoint, Matrix.mul_sub, Matrix.sub_mul, Finset.sum_sub_distrib]
end QuantumInfo.Channel
