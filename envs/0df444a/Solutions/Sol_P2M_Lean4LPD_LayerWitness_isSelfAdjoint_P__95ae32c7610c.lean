-- Prove2me | solution 1 for P2M_Lean4LPD_LayerWitness_isSelfAdjoint_P__95ae32c7610c
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:13:32.656561+00:00
-- url     : https://prove2.me/submissions/45187a7e-4617-4789-80d3-ff61a9ba6a26

module
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Weight
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_LayerWitness
public import Theorems.Thm_Lean4LPD_PauliString_isSelfAdjoint_iff_phase


set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD
open Lean4LPD.LayerWitness
open PauliString
namespace Lean4LPD.LayerWitness
theorem _root_.solution : IsSelfAdjoint P₄ := isSelfAdjoint_iff_phase.2 (by decide)
end Lean4LPD.LayerWitness
