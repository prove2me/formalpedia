-- Prove2me | solution 1 for QEC.Semantics.FiniteInstrument.tensorPowerShortageMass_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T20:23:01.473608+00:00
-- url     : https://prove2.me/submissions/70397ed5-8e7b-42f1-b4fa-5bb7e4bd2320

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
    0 ≤ I.tensorPowerShortageMass accepts attempts required rho := by
  unfold tensorPowerShortageMass
  exact Finset.sum_nonneg fun history _ =>
    (I.tensorPower attempts).bornWeight_nonneg history rho
end QEC.Semantics.FiniteInstrument
