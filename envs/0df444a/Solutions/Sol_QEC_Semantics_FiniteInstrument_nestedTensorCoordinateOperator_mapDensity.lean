-- Prove2me | solution 1 for QEC.Semantics.FiniteInstrument.nestedTensorCoordinateOperator_mapDensity
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T20:25:12.642671+00:00
-- url     : https://prove2.me/submissions/1afbee6e-6c53-43c4-ba19-d0a771bab2dc

import Definitions.Def_QEC_Semantics_Instruments_NestedTensor_Power
import Definitions.Def_QEC_Semantics_Instruments_NestedTensor_MarginalBornMass
import Definitions.Def_QEC_Semantics_Instruments_TensorPower_MarginalBranchOperator
import Definitions.Def_QEC_Semantics_Instruments_NestedTensor_MarginalBranchOperator
import Theorems.Thm_QEC_Semantics_FiniteInstrument_tensorPowerCoordinateOperator_mapDensity


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
    (H : Type u) [NormedAddCommGroup H] [InnerProductSpace Complex H]
    [FiniteQuantumSystem H] (branches : Nat) :
    ∀ (depth : Nat) (rho : DensityOperator (nestedTensorCarrier H branches depth))
      (path : nestedTensorPath branches depth),
      (nestedTensorCoordinateOperator H branches depth path).mapDensity rho =
        nestedTensorInputMarginal H branches depth rho path := by
  intro depth
  induction depth generalizing H with
  | zero =>
      intro rho path
      have hpath : path = PUnit.unit := PUnit.ext _ _
      subst path
      rfl
  | succ depth ih =>
      intro rho path
      rcases path with ⟨pathPrefix, trial⟩
      change
        (tensorPowerCoordinateOperator branches trial).mapDensity
            ((nestedTensorCoordinateOperator
              (tensorPowerCarrier H branches) branches depth pathPrefix).mapDensity rho) =
          tensorPowerInputMarginal branches
            (nestedTensorInputMarginal (tensorPowerCarrier H branches)
              branches depth rho pathPrefix) trial
      rw [ih]
      exact tensorPowerCoordinateOperator_mapDensity branches _ trial
end QEC.Semantics.FiniteInstrument
