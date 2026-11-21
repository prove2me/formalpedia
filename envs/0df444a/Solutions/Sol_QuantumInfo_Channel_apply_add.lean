-- Prove2me | solution 1 for QuantumInfo.Channel.apply_add
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T23:47:25.270405+00:00
-- url     : https://prove2.me/submissions/7836d3ce-fefd-4c26-ab7a-7022c53c967e

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
theorem _root_.solution (Φ : Channel n m ι) (ρ σ : Matrix n n ℂ) :
    Φ.apply (ρ + σ) = Φ.apply ρ + Φ.apply σ := by
  simp only [apply, Matrix.mul_add, Matrix.add_mul, Finset.sum_add_distrib]
end QuantumInfo.Channel
