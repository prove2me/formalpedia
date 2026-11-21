-- Prove2me | solution 1 for QuantumInfo.Channel.adjoint_posSemidef
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T23:47:03.14875+00:00
-- url     : https://prove2.me/submissions/61ad2eab-d7bf-4e69-867b-e9c674e37134

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
theorem _root_.solution (Φ : Channel n m ι) {P : Matrix m m ℂ} (hP : P.PosSemidef) :
    (Φ.adjoint P).PosSemidef := by
  rw [adjoint]
  refine Finset.sum_induction _ Matrix.PosSemidef (fun _ _ => Matrix.PosSemidef.add)
    Matrix.PosSemidef.zero (fun i _ => ?_)
  exact hP.conjTranspose_mul_mul_same (Φ.kraus i)
end QuantumInfo.Channel
