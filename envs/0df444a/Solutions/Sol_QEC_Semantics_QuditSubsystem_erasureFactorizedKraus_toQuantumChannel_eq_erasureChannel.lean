-- Prove2me | solution 1 for QEC.Semantics.QuditSubsystem.erasureFactorizedKraus_toQuantumChannel_eq_erasureChannel
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T20:20:34.241025+00:00
-- url     : https://prove2.me/submissions/569e96f9-9ac6-4de7-920c-b97d6107c38f

import Definitions.Def_QEC_Semantics_Entropy_Purification
import Definitions.Def_QEC_Semantics_Entropy_MatrixRelative
import Definitions.Def_QEC_Semantics_ErrorCorrection_QuditReplacement
import Definitions.Def_QEC_Semantics_ErrorCorrection_KLRecovery
import Definitions.Def_QEC_Semantics_ErrorCorrection_Detectability
import Definitions.Def_QEC_Semantics_ErrorCorrection_ReferenceDecoupling
import Theorems.Thm_QEC_Semantics_QuditSubsystem_erasureFactorizedKraus_inducedMap_eq_erasureChannel
import Theorems.Thm_QEC_Locality_quantumChannel_ext
import Theorems.Thm_QEC_Semantics_QuditSubsystem_quantumChannel_ext


set_option autoImplicit false
noncomputable section
open QEC
open QEC.Semantics
open Classical
open DensityOperator
open scoped BigOperators ComplexOrder TensorProduct
universe u v w
open QEC.Semantics.QuditSubsystem
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
variable {q : ι → Nat}
namespace QEC.Semantics.QuditSubsystem
theorem _root_.solution
    (S : QuditSubsystem q) (hComplete : S.erasureFactorizedKraus.Complete) :
    S.erasureFactorizedKraus.toQuantumChannel hComplete = S.erasureChannel := by
  apply quantumChannel_ext
  rw [FiniteKrausFamily.toQuantumChannel_toLinearMap]
  exact S.erasureFactorizedKraus_inducedMap_eq_erasureChannel
end QEC.Semantics.QuditSubsystem
