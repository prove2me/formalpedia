-- Prove2me | solution 1 for QEC.Semantics.FiniteInstrument.quantumChannelTensorPower_mapDensity_productInput
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T14:04:53.937036+00:00
-- url     : https://prove2.me/submissions/35b651a0-019e-4cea-acfe-cf473baad2c9

import Definitions.Def_QEC_Semantics_Instruments_TensorPower_BranchOperator
import Definitions.Def_QEC_Semantics_Channels_Instrument
import Definitions.Def_QEC_Semantics_Instruments_TensorPower_ChannelProduct
import Theorems.Thm_QEC_Semantics_FiniteInstrument_tensorPowerHistory_punit_eq
import Theorems.Thm_QEC_Semantics_FiniteInstrument_tensorPowerBranchOperatorProduct_punit_eq_productInput
import Theorems.Thm_QEC_Semantics_DensityOperator_ext_toOperator
import Theorems.Thm_QEC_Semantics_FiniteInstrument_branchOperator_tensorPower_productInput
import Theorems.Thm_QEC_Semantics_FiniteInstrument_sum_branchOperator_eq_inducedMap
import Theorems.Thm_QEC_Semantics_FiniteInstrument_tensorPower_complete
import Theorems.Thm_QEC_Semantics_QuantumChannel_toFiniteInstrument_complete
import Theorems.Thm_QEC_Semantics_QuantumChannel_toFiniteInstrument_inducedMap_eq


set_option autoImplicit false
universe u v
open QEC
open QEC.Semantics
noncomputable section
open QEC.Semantics.FiniteInstrument
open scoped TensorProduct
variable {H K : Type u}
variable [NormedAddCommGroup H] [InnerProductSpace Complex H]
  [FiniteQuantumSystem H]
variable [NormedAddCommGroup K] [InnerProductSpace Complex K]
  [FiniteQuantumSystem K]
namespace QEC.Semantics.FiniteInstrument
theorem _root_.solution
    (channel : QuantumChannel H K)
    (rho : DensityOperator H)
    (rhoUnit : DensityOperator (tensorPowerCarrier H 0))
    (sigmaUnit : DensityOperator (tensorPowerCarrier K 0))
    (hunit : sigmaUnit.toOperator = rhoUnit.toOperator)
    (attempts : Nat) :
    ((((channel.toFiniteInstrument).tensorPower attempts).kraus.toQuantumChannel
          ((channel.toFiniteInstrument).tensorPower_complete
            channel.toFiniteInstrument_complete attempts)).mapDensity
        (tensorPowerProductInput rho rhoUnit attempts)).toOperator =
      (tensorPowerProductInput (channel.mapDensity rho) sigmaUnit attempts).toOperator := by
  let I := channel.toFiniteInstrument
  let history : tensorPowerHistory PUnit attempts :=
    tensorPowerHistoryOf PUnit attempts (fun _ => PUnit.unit)
  have hbranch :
      (I.tensorPower attempts).branchOperator history
          (tensorPowerProductInput rho rhoUnit attempts).toOperator =
        tensorPowerBranchOperatorProduct
          (fun outcome => I.branchOperator outcome rho.toOperator)
          rhoUnit.toOperator attempts history :=
    branchOperator_tensorPower_productInput I rho rhoUnit attempts history
  rw [QuantumChannel.mapDensity_toOperator,
    FiniteKrausFamily.toQuantumChannel_apply,
    ← (I.tensorPower attempts).sum_branchOperator_eq_inducedMap]
  rw [Fintype.sum_eq_single history]
  · rw [hbranch]
    have hproduct := tensorPowerBranchOperatorProduct_punit_eq_productInput I
      channel.toFiniteInstrument_complete rho rhoUnit sigmaUnit hunit attempts
    have hmap :
        (I.kraus.toQuantumChannel channel.toFiniteInstrument_complete).mapDensity rho =
          channel.mapDensity rho := by
      apply DensityOperator.ext_toOperator
      exact LinearMap.congr_fun channel.toFiniteInstrument_inducedMap_eq rho.toOperator
    rw [tensorPowerHistory_punit_eq attempts history]
    rw [hmap] at hproduct
    exact hproduct
  · intro other hne
    exact False.elim (hne (tensorPowerHistory_punit_eq attempts other))
end QEC.Semantics.FiniteInstrument
