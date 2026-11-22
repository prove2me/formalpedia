-- Prove2me | solution 1 for P2M_Lean4LPD_LayerWitness_support_P__3172efb66519
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:13:50.748221+00:00
-- url     : https://prove2.me/submissions/b4918e52-da00-4a16-b4fc-5fcc6cad2787

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
theorem _root_.solution : P₆.support = {0, 1, 2, 3, 4, 5} := by decide
end Lean4LPD.LayerWitness
