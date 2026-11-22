-- Prove2me | solution 1 for P2M_Auto_HeatData_T_update___6afbb602a2e7
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T19:14:33.51673+00:00
-- url     : https://prove2.me/submissions/cd897fd9-d51a-4192-8f48-029ecd1cc9a3

module
public import Mathlib
public import Definitions.Def_Triangular_Defs
public import Definitions.Def_Triangular_Auto_TriangularHT
public import Theorems.Thm_Auto_HeatData_T_eq_wGram
public import Theorems.Thm_P2M_Auto_HeatData_w_update_self___e5e807597e26
public import Theorems.Thm_P2M_Auto_HeatData_Brow_update___289bec5b5b62

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
theorem _root_.solution (hh : 0 ≤ Hd.h) {v : Fin 3} {τ : ℝ} (hτ : 0 < τ) :
    Hd.T p (Function.update σ v τ) v = 0 + wGram (Hd.Brow p σ v) (gweight Hd.u Hd.h τ (p v)) := by
  rw [T_eq_wGram Hd p _ hh (by simpa using hτ), Brow_update_σ, w_update_self_σ, zero_add]
end Auto.HeatData
