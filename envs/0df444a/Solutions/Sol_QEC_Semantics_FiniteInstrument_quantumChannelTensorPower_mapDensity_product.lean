-- Prove2me | solution 1 for QEC.Semantics.FiniteInstrument.quantumChannelTensorPower_mapDensity_product
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T14:09:17.095201+00:00
-- url     : https://prove2.me/submissions/8609882a-9a46-469f-8822-b833420e2ef9

import Definitions.Def_QEC_Semantics_Instruments_TensorPower_ChannelProduct
import Definitions.Def_QEC_Semantics_Entropy_Purification
import Definitions.Def_QEC_Semantics_Instruments_TensorPower_ChannelProductFunctorial
import Theorems.Thm_QEC_Semantics_FiniteInstrument_quantumChannelTensorPower_mapDensity_productInput_eq


set_option autoImplicit false
universe u v w x y
open QEC
open QEC.Semantics
noncomputable section
open QEC.Semantics.FiniteInstrument
open scoped BigOperators TensorProduct
variable {H K L : Type u}
variable [NormedAddCommGroup H] [InnerProductSpace Complex H]
  [FiniteQuantumSystem H]
variable [NormedAddCommGroup K] [InnerProductSpace Complex K]
  [FiniteQuantumSystem K]
variable [NormedAddCommGroup L] [InnerProductSpace Complex L]
  [FiniteQuantumSystem L]
namespace QEC.Semantics.FiniteInstrument
theorem _root_.solution
    (channel : QuantumChannel H K)
    (rho : DensityOperator H)
    (rhoUnit : DensityOperator (tensorPowerCarrier H 0))
    (sigmaUnit : DensityOperator (tensorPowerCarrier K 0))
    (hunit : sigmaUnit.toOperator = rhoUnit.toOperator)
    (attempts : Nat) :
    (quantumChannelTensorPower channel attempts).mapDensity
        (tensorPowerProductInput rho rhoUnit attempts) =
      tensorPowerProductInput (channel.mapDensity rho) sigmaUnit attempts := by
  exact quantumChannelTensorPower_mapDensity_productInput_eq
    channel rho rhoUnit sigmaUnit hunit attempts
end QEC.Semantics.FiniteInstrument
