-- Prove2me | solution 1 for QEC.Semantics.FiniteInstrument.nestedTensorPower_bornWeight_path_failure_sum_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T14:09:43.077403+00:00
-- url     : https://prove2.me/submissions/5203787d-cfc9-4231-a56b-72ac856832aa

import Definitions.Def_QEC_Semantics_Instruments_NestedTensor_Power
import Definitions.Def_QEC_Semantics_Instruments_Tensor_MarginalBornMass
import Definitions.Def_QEC_Semantics_Instruments_NestedTensor_MarginalBornMass
import Theorems.Thm_QEC_Semantics_FiniteInstrument_tensorPower_bornWeight_coordinate_failure_sum_eq
import Theorems.Thm_QEC_Semantics_FiniteInstrument_tensorPower_complete


set_option autoImplicit false
universe u v w
open QEC
open QEC.Semantics
open Classical
open scoped BigOperators
noncomputable section
open QEC.Semantics.FiniteInstrument
variable {kappa : Type v} [Fintype kappa]
variable {Omega : Type w} [Fintype Omega]
variable {H K : Type u}
variable [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
variable [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
namespace QEC.Semantics.FiniteInstrument
theorem _root_.solution
    (I : FiniteInstrument kappa Omega H K) (hI : I.kraus.Complete)
    (fails : Omega -> Prop) [DecidablePred fails] (branches : Nat) :
    ∀ (depth : Nat)
      (rho : DensityOperator (nestedTensorCarrier H branches depth))
      (path : nestedTensorPath branches depth),
      (∑ history ∈ Finset.univ.filter
          (fun history : nestedTensorHistory Omega branches depth =>
            fails (nestedTensorHistoryAt Omega branches depth history path)),
        (nestedTensorPower I branches depth).bornWeight history rho) =
        ∑ outcome ∈ Finset.univ.filter fails,
          I.bornWeight outcome
            (nestedTensorInputMarginal H branches depth rho path) := by
  intro depth
  induction depth generalizing kappa Omega H K with
  | zero =>
      intro rho path
      have hpath : path = PUnit.unit := PUnit.ext _ _
      subst path
      rfl
  | succ depth ih =>
      intro rho path
      rcases path with ⟨pathPrefix, trial⟩
      change
        (∑ history ∈ Finset.univ.filter
            (fun history : nestedTensorHistory
                (tensorPowerHistory Omega branches) branches depth =>
              fails
                (tensorPowerHistoryAt Omega branches
                  (nestedTensorHistoryAt (tensorPowerHistory Omega branches)
                    branches depth history pathPrefix) trial)),
          (nestedTensorPower (I.tensorPower branches) branches depth).bornWeight
            history rho) =
          ∑ outcome ∈ Finset.univ.filter fails,
            I.bornWeight outcome
              (tensorPowerInputMarginal branches
                (nestedTensorInputMarginal
                  (tensorPowerCarrier H branches)
                  branches depth rho pathPrefix) trial)
      rw [ih
        (I := I.tensorPower branches)
        (hI := I.tensorPower_complete hI branches)
        (fails := fun layer =>
          fails (tensorPowerHistoryAt Omega branches layer trial))
        (rho := rho) (path := pathPrefix)]
      exact tensorPower_bornWeight_coordinate_failure_sum_eq
        I hI fails branches
          (nestedTensorInputMarginal (tensorPowerCarrier H branches)
            branches depth rho pathPrefix) trial
end QEC.Semantics.FiniteInstrument
