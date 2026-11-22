-- Prove2me | solution 1 for P2M_Auto_HeatData_Bnext_update___37794f5ef3ab
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T18:44:37.292453+00:00
-- url     : https://prove2.me/submissions/f55942bb-0780-4f14-9eab-63fffc695fec

module
public import Mathlib
public import Definitions.Def_Triangular_Defs
public import Definitions.Def_Triangular_Auto_TriangularHT
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
theorem _root_.solution {v k : Fin 3} (hk : k ≠ v) (τ : ℝ) :
    Hd.Bnext p (Function.update σ k τ) v = Hd.Bnext p σ v := by
  simp [Bnext, sq_update_ne_σ Hd p σ hk.symm]
end Auto.HeatData
