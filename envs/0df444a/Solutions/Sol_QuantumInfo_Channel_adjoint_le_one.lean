-- Prove2me | solution 1 for QuantumInfo.Channel.adjoint_le_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T23:47:47.199057+00:00
-- url     : https://prove2.me/submissions/42a3d833-9ea8-4d24-b6a5-f7ff56a97373

module
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.Data.Complex.Basic
public import Mathlib.Analysis.Complex.Order
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Analysis.Matrix.PosDef
public import Definitions.Def_KnillLaflammeLean_QuantumInfo_Channel
public import Theorems.Thm_QuantumInfo_Channel_adjoint_unital
public import Theorems.Thm_QuantumInfo_Channel_adjoint_posSemidef
public import Theorems.Thm_QuantumInfo_Channel_adjoint_sub

set_option autoImplicit false
@[expose] public section
public section
open Matrix
open scoped ComplexOrder
open QuantumInfo
open QuantumInfo.Channel
variable {n m ι : Type*} [Fintype n] [Fintype m] [Fintype ι] [DecidableEq n]
namespace QuantumInfo.Channel
theorem _root_.solution [DecidableEq m] (Φ : Channel n m ι) {P : Matrix m m ℂ}
    (_hP : P.PosSemidef) (hP' : ((1 : Matrix m m ℂ) - P).PosSemidef) :
    ((1 : Matrix n n ℂ) - Φ.adjoint P).PosSemidef := by
  rw [← Φ.adjoint_unital, ← Φ.adjoint_sub]
  exact Φ.adjoint_posSemidef hP'
end QuantumInfo.Channel
