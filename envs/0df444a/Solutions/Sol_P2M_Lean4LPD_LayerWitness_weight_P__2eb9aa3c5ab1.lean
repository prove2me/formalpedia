-- Prove2me | solution 1 for P2M_Lean4LPD_LayerWitness_weight_P__2eb9aa3c5ab1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:10:10.084359+00:00
-- url     : https://prove2.me/submissions/c40a2a60-e819-4f45-9678-9cf0f34e6413

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
theorem _root_.solution : P₄.weight = 4 := by decide
end Lean4LPD.LayerWitness
