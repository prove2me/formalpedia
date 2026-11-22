-- Prove2me | solution 1 for P2M_Lean4LPD_LayerWitness_isLayer_L__a95698ae6318
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:09:43.374598+00:00
-- url     : https://prove2.me/submissions/37ed7a4c-62c4-43f7-a75c-9a152428dea3

module
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Weight
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_LayerWitness

set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD
open Lean4LPD.LayerWitness
open PauliString
namespace Lean4LPD.LayerWitness
theorem _root_.solution : IsLayer 2 L₁ := ⟨by decide, by decide⟩
end Lean4LPD.LayerWitness
