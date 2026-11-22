-- Prove2me | solution 1 for P2M_Auto_fromBlocks_sub__68b4b78d801e
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T19:17:27.788648+00:00
-- url     : https://prove2.me/submissions/366defa4-4ed4-4a41-9ebf-354c21272966

module
public import Mathlib
public import Definitions.Def_Triangular_Defs
public import Definitions.Def_Triangular_Auto_TriangularHT

set_option autoImplicit true
@[expose] public section
public section
public section
open scoped MatrixOrder Matrix.Norms.L2Operator ComplexOrder ENNReal NNReal
open Matrix MeasureTheory Filter Topology
public section
open scoped MatrixOrder Matrix.Norms.L2Operator ComplexOrder ENNReal NNReal
open Matrix MeasureTheory Filter Topology Real
open Auto
noncomputable section
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
omit [Fintype ι] [DecidableEq ι]
namespace Auto
theorem _root_.solution (a b c d a' b' c' d' : Matrix ι ι ℂ) :
    Matrix.fromBlocks a b c d - Matrix.fromBlocks a' b' c' d' = Matrix.fromBlocks (a - a') (b -
      b') (c - c') (d - d') := by
  simp [sub_eq_add_neg, Matrix.fromBlocks_neg, Matrix.fromBlocks_add]
end Auto
