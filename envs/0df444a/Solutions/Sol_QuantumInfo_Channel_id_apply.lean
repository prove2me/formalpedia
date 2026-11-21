-- Prove2me | solution 1 for QuantumInfo.Channel.id_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T23:47:00.445042+00:00
-- url     : https://prove2.me/submissions/42ebc427-d67e-4dda-aeb7-d57484b3b86a

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
theorem _root_.solution (n : Type*) [Fintype n] [DecidableEq n] (ρ : Matrix n n ℂ) :
    (Channel.id n).apply ρ = ρ := by
  simp [apply, Channel.id]
end QuantumInfo.Channel
