-- Prove2me | solution 1 for P2M_Auto_continuous_gaussian__66693ed17080
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T18:25:09.065907+00:00
-- url     : https://prove2.me/submissions/deaa96d2-ac55-4587-9c74-42386f195ec8

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
namespace Auto
theorem _root_.solution (σ : ℝ) : Continuous (gaussian σ) := by
  have := continuous_gaussianD 0 σ
  rwa [gaussianD_zero] at this
end Auto
