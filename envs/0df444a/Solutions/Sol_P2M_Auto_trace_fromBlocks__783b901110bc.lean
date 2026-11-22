-- Prove2me | solution 1 for P2M_Auto_trace_fromBlocks__783b901110bc
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T19:16:16.904155+00:00
-- url     : https://prove2.me/submissions/f4979f59-ca60-4bd6-8aea-3e610930f9b3

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
omit [DecidableEq ι]
namespace Auto
theorem _root_.solution (a b c d : Matrix ι ι ℂ) :
    (Matrix.fromBlocks a b c d).trace = a.trace + d.trace := by
  simp [Matrix.trace, Fintype.sum_sum_type]
end Auto
