-- Prove2me | solution 1 for QuantumInfo.Channel.adjoint_trace_mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T23:47:40.117453+00:00
-- url     : https://prove2.me/submissions/e6f0bfe5-2bd5-4124-bf52-9c595dd60d6d

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
theorem _root_.solution (Φ : Channel n m ι) (P : Matrix m m ℂ) (ρ : Matrix n n ℂ) :
    (P * Φ.apply ρ).trace = (Φ.adjoint P * ρ).trace := by
  rw [apply, Finset.mul_sum, Matrix.trace_sum, adjoint, Finset.sum_mul, Matrix.trace_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  -- Tr(P · (Kᵢ ρ) · Kᵢᴴ) = Tr(Kᵢᴴ · P · (Kᵢ ρ)): rotate Kᵢᴴ to the front (cyclicity).
  rw [show P * (Φ.kraus i * ρ * (Φ.kraus i)ᴴ) = P * (Φ.kraus i * ρ) * (Φ.kraus i)ᴴ by
        rw [Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_assoc],
    Matrix.trace_mul_cycle P (Φ.kraus i * ρ) (Φ.kraus i)ᴴ,
    show (Φ.kraus i)ᴴ * P * (Φ.kraus i) * ρ
        = (Φ.kraus i)ᴴ * P * (Φ.kraus i * ρ) by rw [Matrix.mul_assoc]]
end QuantumInfo.Channel
