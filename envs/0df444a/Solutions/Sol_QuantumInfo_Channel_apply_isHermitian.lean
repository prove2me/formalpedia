-- Prove2me | solution 1 for QuantumInfo.Channel.apply_isHermitian
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T23:47:31.056327+00:00
-- url     : https://prove2.me/submissions/7e7b8945-593b-40f5-b249-fc1a83a149db

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
theorem _root_.solution (Φ : Channel n m ι) {ρ : Matrix n n ℂ} (hρ : ρ.IsHermitian) :
    (Φ.apply ρ).IsHermitian := by
  unfold Matrix.IsHermitian apply
  rw [Matrix.conjTranspose_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
    hρ.eq, Matrix.mul_assoc]
end QuantumInfo.Channel
