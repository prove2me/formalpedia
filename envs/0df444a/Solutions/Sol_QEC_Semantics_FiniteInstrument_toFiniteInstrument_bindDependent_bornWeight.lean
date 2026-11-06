-- Prove2me | solution 1 for QEC.Semantics.FiniteInstrument.toFiniteInstrument_bindDependent_bornWeight
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T20:24:24.180039+00:00
-- url     : https://prove2.me/submissions/13b8eaad-6874-4e6a-ba7e-ce842457ffc1

import Definitions.Def_QEC_Semantics_Instruments_TensorPower_Basis
import Definitions.Def_QEC_Semantics_Instruments_TensorPower_BornMass
import Definitions.Def_QEC_Semantics_Instruments_TensorPower_BranchOperator
import Theorems.Thm_QEC_Semantics_FiniteInstrument_bindDependent_branchOperator_fst_punit
import Theorems.Thm_QEC_Semantics_QuantumChannel_toFiniteInstrument_inducedMap_apply


set_option autoImplicit false
universe u v w x y
open QEC
open QEC.Semantics
open Classical
open scoped BigOperators ComplexOrder TensorProduct
noncomputable section
open QEC.Semantics.FiniteInstrument
variable {κ : Type v} [Fintype κ]
variable {Ω : Type w} [Fintype Ω]
variable {H K : Type u}
variable [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
variable [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
variable {κ' : Type x} [Fintype κ']
variable {L : Type u}
variable [NormedAddCommGroup L] [InnerProductSpace Complex L] [FiniteQuantumSystem L]
namespace QEC.Semantics.FiniteInstrument
theorem _root_.solution
    (Phi : QuantumChannel H K) (J : FiniteInstrument κ' Ω K L)
    (outcome : Ω) (rho : DensityOperator H) :
    (Phi.toFiniteInstrument.bindDependent (fun _ => J)).bornWeight
        ⟨PUnit.unit, outcome⟩ rho =
      J.bornWeight outcome (Phi.mapDensity rho) := by
  unfold bornWeight
  rw [bindDependent_branchOperator_fst_punit]
  rw [QuantumChannel.toFiniteInstrument_inducedMap_apply]
  rfl
end QEC.Semantics.FiniteInstrument
