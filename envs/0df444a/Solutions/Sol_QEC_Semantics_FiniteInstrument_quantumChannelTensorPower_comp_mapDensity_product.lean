-- Prove2me | solution 1 for QEC.Semantics.FiniteInstrument.quantumChannelTensorPower_comp_mapDensity_product
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T20:27:08.824559+00:00
-- url     : https://prove2.me/submissions/db1446ae-33b5-4837-b3a5-651a1db4f0de

import Definitions.Def_QEC_Semantics_Instruments_TensorPower_ChannelProduct
import Definitions.Def_QEC_Semantics_Entropy_Purification
import Definitions.Def_QEC_Semantics_Instruments_TensorPower_ChannelProductFunctorial
import Theorems.Thm_QEC_Semantics_FiniteInstrument_quantumChannelTensorPower_mapDensity_product

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
    (first : QuantumChannel H K) (second : QuantumChannel K L)
    (rho : DensityOperator H)
    (rhoUnit : DensityOperator (tensorPowerCarrier H 0))
    (sigmaUnit : DensityOperator (tensorPowerCarrier K 0))
    (tauUnit : DensityOperator (tensorPowerCarrier L 0))
    (hsigma : sigmaUnit.toOperator = rhoUnit.toOperator)
    (htau : tauUnit.toOperator = sigmaUnit.toOperator)
    (attempts : Nat) :
    (quantumChannelTensorPower second attempts).mapDensity
        ((quantumChannelTensorPower first attempts).mapDensity
          (tensorPowerProductInput rho rhoUnit attempts)) =
      tensorPowerProductInput
        ((QuantumChannel.comp second first).mapDensity rho)
        tauUnit attempts := by
  rw [quantumChannelTensorPower_mapDensity_product
    first rho rhoUnit sigmaUnit hsigma attempts]
  rw [quantumChannelTensorPower_mapDensity_product
    second (first.mapDensity rho) sigmaUnit tauUnit htau attempts]
  rfl
end QEC.Semantics.FiniteInstrument
