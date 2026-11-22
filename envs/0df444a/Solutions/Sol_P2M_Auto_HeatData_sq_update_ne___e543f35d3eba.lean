-- Prove2me | solution 1 for P2M_Auto_HeatData_sq_update_ne___e543f35d3eba
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T18:33:13.560827+00:00
-- url     : https://prove2.me/submissions/bef667a5-1805-4c86-bd47-2fee6e1dead0

module
public import Mathlib
public import Definitions.Def_Triangular_Defs
public import Definitions.Def_Triangular_Auto_TriangularHT
public import Theorems.Thm_P2M_Auto_HeatData_w_update_ne___7eef3067864c

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
    Hd.sqw p (Function.update σ v τ) k = Hd.sqw p σ k := by
  unfold HeatData.sqw; rw [w_update_ne_σ Hd p σ hk]
end Auto.HeatData
