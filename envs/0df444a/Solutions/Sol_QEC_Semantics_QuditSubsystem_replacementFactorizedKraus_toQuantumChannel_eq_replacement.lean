-- Prove2me | solution 1 for QEC.Semantics.QuditSubsystem.replacementFactorizedKraus_toQuantumChannel_eq_replacement
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T20:18:38.433467+00:00
-- url     : https://prove2.me/submissions/3cdc3096-4bd2-46fc-8c77-4001549f6c47

import Definitions.Def_QEC_Semantics_ErrorCorrection_QuditReplacement
import Definitions.Def_QEC_Semantics_ErrorCorrection_KLRecovery
import Definitions.Def_QEC_Semantics_ErrorCorrection_CodeSupport
import Definitions.Def_QEC_Semantics_ErrorCorrection_Detectability
import Definitions.Def_QEC_Semantics_ErrorCorrection_QuditNoInformation
import Theorems.Thm_QEC_Semantics_QuditSubsystem_replacementFactorizedKraus_inducedMap_eq_replacement
import Theorems.Thm_QEC_Semantics_QuditSubsystem_quantumChannel_ext


set_option autoImplicit false
noncomputable section
open QEC
open QEC.Semantics
open Classical
open scoped BigOperators ComplexOrder TensorProduct
universe u v
open QEC.Semantics.QuditSubsystem
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
variable {q : ι → Nat}
namespace QEC.Semantics.QuditSubsystem
theorem _root_.solution (S : QuditSubsystem q)
    (rho : DensityOperator S.selectedSystem)
    (hComplete : (S.replacementFactorizedKraus rho).Complete) :
    (S.replacementFactorizedKraus rho).toQuantumChannel hComplete =
      QuantumChannel.comp (S.prepareFactorized rho) S.erasureChannel := by
  apply quantumChannel_ext
  rw [FiniteKrausFamily.toQuantumChannel_toLinearMap]
  exact S.replacementFactorizedKraus_inducedMap_eq_replacement rho
end QEC.Semantics.QuditSubsystem
