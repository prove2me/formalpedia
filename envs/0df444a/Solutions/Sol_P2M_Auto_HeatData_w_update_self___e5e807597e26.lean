-- Prove2me | solution 1 for P2M_Auto_HeatData_w_update_self___e5e807597e26
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T18:32:23.914405+00:00
-- url     : https://prove2.me/submissions/7b8a347b-39d5-440a-a305-be1c62c0a5b5

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
open Auto.HeatData
variable (Hd : HeatData ι) (p σ : Fin 3 → ℝ)
omit [Fintype ι] [DecidableEq ι]
namespace Auto.HeatData
theorem _root_.solution (v : Fin 3) (τ : ℝ) :
    Hd.w p (Function.update σ v τ) v = gweight Hd.u Hd.h τ (p v) := by
  simp [w]
end Auto.HeatData
