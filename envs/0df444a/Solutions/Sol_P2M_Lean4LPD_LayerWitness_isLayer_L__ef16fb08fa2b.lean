-- Prove2me | solution 1 for P2M_Lean4LPD_LayerWitness_isLayer_L__ef16fb08fa2b
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:09:43.758374+00:00
-- url     : https://prove2.me/submissions/9c1d0478-9ef2-4c4a-9e05-19145ca9c7cb

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
theorem _root_.solution : IsLayer 2 L₂ := ⟨by decide, by decide⟩
end Lean4LPD.LayerWitness
