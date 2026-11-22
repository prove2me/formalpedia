-- Prove2me | solution 1 for P2M_Lean4LPD_LayerWitness_P__mem_reachable_unmerged_3e0878106649
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:11:18.973466+00:00
-- url     : https://prove2.me/submissions/57e7d45c-d45c-4d50-8409-347a15a60de7

module
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Weight
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_LayerWitness
public import Theorems.Thm_Lean4LPD_PauliString_reachable_subset_cons
public import Theorems.Thm_Lean4LPD_PauliString_reachable_subset_reachable_cons
public import Theorems.Thm_P2M_Lean4LPD_LayerWitness_P__mem_reachable_cc8d734340ab

set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD
open Lean4LPD.LayerWitness
open PauliString
namespace Lean4LPD.LayerWitness
theorem _root_.solution : P₆ ∈ reachable (layers := [L₁, L₂, L₂, L₁]) (Z 3) :=
  reachable_subset_reachable_cons
    (reachable_subset_reachable_cons (reachable_subset_cons L₂ [L₁]) L₂) L₁ (Z 3)
    P₆_mem_reachable
end Lean4LPD.LayerWitness
