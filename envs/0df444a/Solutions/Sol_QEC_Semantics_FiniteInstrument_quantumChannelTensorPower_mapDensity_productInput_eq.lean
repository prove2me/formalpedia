-- Prove2me | solution 1 for QEC.Semantics.FiniteInstrument.quantumChannelTensorPower_mapDensity_productInput_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T14:07:15.872948+00:00
-- url     : https://prove2.me/submissions/e1203ecb-351e-46fd-ba5c-3008ede5c11b

import Definitions.Def_QEC_Semantics_Instruments_TensorPower_BranchOperator
import Definitions.Def_QEC_Semantics_Channels_Instrument
import Definitions.Def_QEC_Semantics_Instruments_TensorPower_ChannelProduct
import Theorems.Thm_QEC_Semantics_FiniteInstrument_quantumChannelTensorPower_mapDensity_productInput
import Theorems.Thm_QEC_Semantics_DensityOperator_ext_toOperator
import Theorems.Thm_QEC_Semantics_FiniteInstrument_tensorPower_complete
import Theorems.Thm_QEC_Semantics_QuantumChannel_toFiniteInstrument_complete


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
    (((channel.toFiniteInstrument).tensorPower attempts).kraus.toQuantumChannel
          ((channel.toFiniteInstrument).tensorPower_complete
            channel.toFiniteInstrument_complete attempts)).mapDensity
        (tensorPowerProductInput rho rhoUnit attempts) =
      tensorPowerProductInput (channel.mapDensity rho) sigmaUnit attempts := by
  apply DensityOperator.ext_toOperator
  exact quantumChannelTensorPower_mapDensity_productInput
    channel rho rhoUnit sigmaUnit hunit attempts
end QEC.Semantics.FiniteInstrument
