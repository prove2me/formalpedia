-- Prove2me | solution 1 for P2M_Auto_HeatData_w_update_ne___7eef3067864c
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T18:32:06.058253+00:00
-- url     : https://prove2.me/submissions/6a6282b3-044a-4222-85ed-29466aec86d6

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
theorem _root_.solution {v k : Fin 3} (hk : k ≠ v) (τ : ℝ) :
    Hd.w p (Function.update σ v τ) k = Hd.w p σ k := by
  simp [w, Function.update_of_ne hk]
end Auto.HeatData
