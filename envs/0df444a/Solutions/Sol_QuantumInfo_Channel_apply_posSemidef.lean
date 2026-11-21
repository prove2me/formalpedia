-- Prove2me | solution 1 for QuantumInfo.Channel.apply_posSemidef
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T23:47:28.115808+00:00
-- url     : https://prove2.me/submissions/32b25160-0525-45a3-8da9-274b1853c803

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
theorem _root_.solution (Φ : Channel n m ι) {ρ : Matrix n n ℂ} (hρ : ρ.PosSemidef) :
    (Φ.apply ρ).PosSemidef := by
  rw [apply]
  refine Finset.sum_induction _ Matrix.PosSemidef (fun _ _ => Matrix.PosSemidef.add)
    Matrix.PosSemidef.zero (fun i _ => ?_)
  exact hρ.mul_mul_conjTranspose_same (Φ.kraus i)
end QuantumInfo.Channel
