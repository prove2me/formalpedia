-- Prove2me | solution 1 for P2M_Lean4LPD_LayerWitness_P__mem_reachable_4ba0f0956398
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:10:14.788689+00:00
-- url     : https://prove2.me/submissions/00a9ed64-d741-4dd2-8467-12bc137e13bd

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
theorem _root_.solution : P₄ ∈ reachable (layers := [L₁, L₂]) (Z 3) := by decide
end Lean4LPD.LayerWitness
