-- Prove2me | solution 1 for QuantumInfo.Channel.apply_trace
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T23:47:01.554356+00:00
-- url     : https://prove2.me/submissions/9dd89d62-2be3-45aa-b1e4-b5f973682350

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
theorem _root_.solution (Φ : Channel n m ι) (ρ : Matrix n n ℂ) :
    (Φ.apply ρ).trace = ρ.trace := by
  simp only [apply, Matrix.trace_sum]
  simp_rw [Matrix.trace_mul_cycle (Φ.kraus _) ρ (Φ.kraus _)ᴴ]
  rw [← Matrix.trace_sum, ← Finset.sum_mul, Φ.tp, Matrix.one_mul]
end QuantumInfo.Channel
