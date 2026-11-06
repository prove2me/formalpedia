-- Prove2me | solution 1 for QEC.Semantics.FiniteInstrument.tensorPowerShortageMass_markov_le_rejectedBornWeight
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T20:37:45.197992+00:00
-- url     : https://prove2.me/submissions/bbdd97d4-1bc6-4382-a21f-ec72aff78f7c

import Definitions.Def_QEC_Semantics_Instruments_TensorPower_BornMass
import Definitions.Def_QEC_Semantics_Instruments_TensorPower_FirstMoment
import Theorems.Thm_QEC_Semantics_FiniteInstrument_tensorPowerShortage_rejectedCount_lower_bound
import Theorems.Thm_QEC_Semantics_FiniteInstrument_tensorPowerRejectedFirstMoment_eq_attempts_mul_rejectedBornWeight
import Theorems.Thm_QEC_Semantics_FiniteInstrument_bornWeight_nonneg
import Theorems.Thm_QEC_Semantics_FiniteInstrument_bornWeight_tensorPower


set_option autoImplicit false
universe u v w
open QEC
open QEC.Semantics
open scoped BigOperators
noncomputable section
open QEC.Semantics.FiniteInstrument
namespace QEC.Semantics.FiniteInstrument
theorem _root_.solution
    {κ : Type v} [Fintype κ] {Ω : Type w} [Fintype Ω] {H K : Type u}
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
    (I : FiniteInstrument κ Ω H K) (accepts : Ω → Prop) [DecidablePred accepts]
    (hI : I.kraus.Complete) (rho : DensityOperator H)
    (rhoUnit : DensityOperator (tensorPowerCarrier H 0))
    (attempts required : Nat) (hrequired : required ≤ attempts) :
    ((attempts - required + 1 : Nat) : ℝ) *
        I.tensorPowerShortageMass accepts attempts required
          (tensorPowerProductInput rho rhoUnit attempts) ≤
      (attempts : ℝ) *
        ∑ outcome ∈ Finset.univ.filter (fun outcome => ¬ accepts outcome),
          I.bornWeight outcome rho := by
  let productInput := tensorPowerProductInput rho rhoUnit attempts
  calc
    _ = ∑ history ∈ Finset.univ.filter
        (fun history =>
          (tensorPowerAcceptedIndices accepts attempts history).card < required),
        ((attempts - required + 1 : Nat) : ℝ) *
          (I.tensorPower attempts).bornWeight history productInput := by
      unfold tensorPowerShortageMass
      rw [Finset.mul_sum]
    _ ≤ ∑ history ∈ Finset.univ.filter
        (fun history =>
          (tensorPowerAcceptedIndices accepts attempts history).card < required),
        (tensorPowerRejectedCount accepts attempts history : ℝ) *
          (I.tensorPower attempts).bornWeight history productInput := by
      apply Finset.sum_le_sum
      intro history hhistory
      have hshort := (Finset.mem_filter.mp hhistory).2
      have hcount : ((attempts - required + 1 : Nat) : ℝ) ≤
          (tensorPowerRejectedCount accepts attempts history : ℝ) := by
        exact_mod_cast tensorPowerShortage_rejectedCount_lower_bound accepts attempts required
          history hrequired hshort
      exact mul_le_mul_of_nonneg_right hcount
        ((I.tensorPower attempts).bornWeight_nonneg history productInput)
    _ ≤ ∑ history : tensorPowerHistory Ω attempts,
        (tensorPowerRejectedCount accepts attempts history : ℝ) *
          (I.tensorPower attempts).bornWeight history productInput := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      intro history _ _
      exact mul_nonneg (Nat.cast_nonneg _)
        ((I.tensorPower attempts).bornWeight_nonneg history productInput)
    _ = tensorPowerRejectedFirstMoment I accepts rho rhoUnit attempts := by
      unfold tensorPowerRejectedFirstMoment
      apply Finset.sum_congr rfl
      intro history _
      rw [bornWeight_tensorPower]
    _ = _ := tensorPowerRejectedFirstMoment_eq_attempts_mul_rejectedBornWeight
      I accepts hI rho rhoUnit attempts
end QEC.Semantics.FiniteInstrument
