-- Prove2me | solution 1 for P2M_Auto_HeatData_Brow_update___289bec5b5b62
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T18:44:34.187313+00:00
-- url     : https://prove2.me/submissions/252ac60f-5cba-43d4-b654-53dec16bba76

module
public import Mathlib
public import Definitions.Def_Triangular_Defs
public import Definitions.Def_Triangular_Auto_TriangularHT
public import Theorems.Thm_Auto_HeatData_fin3_ne_succ
public import Theorems.Thm_Auto_HeatData_fin3_ne_pred
public import Theorems.Thm_P2M_Auto_HeatData_sq_update_ne___e543f35d3eba

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
namespace Auto.HeatData
theorem _root_.solution (v : Fin 3) (τ : ℝ) : Hd.Brow p (Function.update σ v τ) v = Hd.Brow p σ v := by
  simp [Brow, Dc, sq_update_ne_σ Hd p σ (fin3_ne_succ v).symm,
    sq_update_ne_σ Hd p σ (fin3_ne_pred v).symm]
end Auto.HeatData
