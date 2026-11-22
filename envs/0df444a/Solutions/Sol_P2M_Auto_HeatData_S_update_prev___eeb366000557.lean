-- Prove2me | solution 1 for P2M_Auto_HeatData_S_update_prev___eeb366000557
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T19:15:52.734243+00:00
-- url     : https://prove2.me/submissions/d60cd5fb-d3fb-4006-be54-5fdba7c78d0f

module
public import Mathlib
public import Definitions.Def_Triangular_Defs
public import Definitions.Def_Triangular_Auto_TriangularHT
public import Theorems.Thm_Auto_HeatData_S_eq_wGram
public import Theorems.Thm_Auto_HeatData_fin3_ne_pred
public import Theorems.Thm_Auto_HeatData_fin3_succ_ne_pred
public import Theorems.Thm_P2M_Auto_HeatData_w_update_ne___7eef3067864c
public import Theorems.Thm_P2M_Auto_HeatData_w_update_self___e5e807597e26
public import Theorems.Thm_P2M_Auto_HeatData_Bnext_update___37794f5ef3ab
public import Theorems.Thm_P2M_Auto_HeatData_Bprev_update___c335d4919a13

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
theorem _root_.solution (hh : 0 ≤ Hd.h) (hσ : ∀ k, 0 < σ k) (v : Fin 3) {τ : ℝ} (hτ : 0 < τ) :
    Hd.S p (Function.update σ (v - 1) τ) v = wGram (Hd.Bnext p σ v) (Hd.w p σ (v + 1)) + wGram
      (Hd.Bprev p σ v) (gweight Hd.u Hd.h τ (p (v - 1))) := by
  rw [S_eq_wGram Hd p _ hh (by
      rw [Function.update_of_ne (fin3_succ_ne_pred v)]; exact hσ _) (by simpa using hτ),
    Bnext_update_σ Hd p σ (fin3_ne_pred v).symm,
    Bprev_update_σ Hd p σ (fin3_ne_pred v).symm, w_update_self_σ,
    w_update_ne_σ Hd p σ (fin3_succ_ne_pred v)]
end Auto.HeatData
