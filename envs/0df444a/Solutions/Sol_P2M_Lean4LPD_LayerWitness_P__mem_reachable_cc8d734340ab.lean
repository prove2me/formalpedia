-- Prove2me | solution 1 for P2M_Lean4LPD_LayerWitness_P__mem_reachable_cc8d734340ab
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:03:05.718098+00:00
-- url     : https://prove2.me/submissions/7e1b79a2-1b01-458d-9f7a-594bd836ea5d

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
theorem _root_.solution : P₆ ∈ reachable (layers := [L₁, L₂, L₁]) (Z 3) := by decide
end Lean4LPD.LayerWitness
