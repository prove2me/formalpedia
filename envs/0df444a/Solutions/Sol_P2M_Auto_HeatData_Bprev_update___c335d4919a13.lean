-- Prove2me | solution 1 for P2M_Auto_HeatData_Bprev_update___c335d4919a13
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T18:44:38.009507+00:00
-- url     : https://prove2.me/submissions/cf3addea-8b90-4a1a-beb8-ae570028f8c9

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
    Hd.Bprev p (Function.update σ k τ) v = Hd.Bprev p σ v := by
  simp [Bprev, sq_update_ne_σ Hd p σ hk.symm]
end Auto.HeatData
