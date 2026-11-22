-- Prove2me | solution 1 for P2M_Lean4LPD_LayerWitness_isSelfAdjoint_L__21e90ea403c3
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:09:47.155478+00:00
-- url     : https://prove2.me/submissions/5737067b-efa5-4e9e-b927-17df45bf7620

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
theorem _root_.solution : ∀ G ∈ L₁, IsSelfAdjoint G := by
  have h : ∀ G ∈ L₁, signPhase (G.z ⬝ᵥ G.x) = 2 * G.phase := by decide
  exact fun G hG => isSelfAdjoint_iff_phase.2 (h G hG)
end Lean4LPD.LayerWitness
