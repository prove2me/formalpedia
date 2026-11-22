-- Prove2me | solution 1 for P2M_Lean4LPD_LayerWitness_support_P__9a4338aca21b
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:13:46.506257+00:00
-- url     : https://prove2.me/submissions/2ecccd99-7038-4a99-8752-24640115a0c5

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
theorem _root_.solution : P₄.support = {1, 2, 3, 4} := by decide
end Lean4LPD.LayerWitness
