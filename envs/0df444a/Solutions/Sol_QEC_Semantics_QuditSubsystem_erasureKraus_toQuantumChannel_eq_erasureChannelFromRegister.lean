-- Prove2me | solution 1 for QEC.Semantics.QuditSubsystem.erasureKraus_toQuantumChannel_eq_erasureChannelFromRegister
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T20:20:35.041274+00:00
-- url     : https://prove2.me/submissions/0843a73e-7a4b-4b9d-b1b7-a3cca149a0e3

import Definitions.Def_QEC_Semantics_Entropy_Purification
import Definitions.Def_QEC_Semantics_Entropy_MatrixRelative
import Definitions.Def_QEC_Semantics_ErrorCorrection_QuditReplacement
import Definitions.Def_QEC_Semantics_ErrorCorrection_KLRecovery
import Definitions.Def_QEC_Semantics_ErrorCorrection_Detectability
import Definitions.Def_QEC_Semantics_ErrorCorrection_ReferenceDecoupling
import Theorems.Thm_QEC_Semantics_QuditSubsystem_erasureKraus_inducedMap_eq_erasureChannelFromRegister
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
    (S : QuditSubsystem q) (hComplete : S.erasureKraus.Complete) :
    S.erasureKraus.toQuantumChannel hComplete = S.erasureChannelFromRegister := by
  apply quantumChannel_ext
  rw [FiniteKrausFamily.toQuantumChannel_toLinearMap]
  exact S.erasureKraus_inducedMap_eq_erasureChannelFromRegister
end QEC.Semantics.QuditSubsystem
