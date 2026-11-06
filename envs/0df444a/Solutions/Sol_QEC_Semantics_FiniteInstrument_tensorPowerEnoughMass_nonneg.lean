-- Prove2me | solution 1 for QEC.Semantics.FiniteInstrument.tensorPowerEnoughMass_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T20:22:44.460909+00:00
-- url     : https://prove2.me/submissions/afbf2cbd-e136-4f58-843b-3b9fbc5fc796

import Definitions.Def_QEC_Semantics_Instruments_TensorPower_ConditionedChannel
import Definitions.Def_QEC_Semantics_Instruments_TensorPower_BornMass
import Theorems.Thm_QEC_Semantics_FiniteInstrument_bornWeight_nonneg


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
namespace QEC.Semantics.FiniteInstrument
theorem _root_.solution (I : FiniteInstrument κ Ω H K)
    (accepts : Ω → Prop) [DecidablePred accepts] (attempts required : Nat)
    (rho : DensityOperator (tensorPowerCarrier H attempts)) :
    0 ≤ I.tensorPowerEnoughMass accepts attempts required rho := by
  unfold tensorPowerEnoughMass
  exact Finset.sum_nonneg fun history _ =>
    (I.tensorPower attempts).bornWeight_nonneg history rho
end QEC.Semantics.FiniteInstrument
