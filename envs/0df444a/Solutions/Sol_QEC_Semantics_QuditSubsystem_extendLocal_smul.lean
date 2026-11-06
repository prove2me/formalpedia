-- Prove2me | solution 1 for QEC.Semantics.QuditSubsystem.extendLocal_smul
-- status  : ACCEPTED   (prove)
-- author  : @dphz
-- created : 2026-11-05T18:13:30.209481+00:00
-- url     : https://prove2.me/submissions/df328c7a-fc7b-44b3-898a-4be79ad88ddb

-- ID: 6ff54ec4-d7f7-4e27-b3b2-50d27edccd20 | NAME: QEC.Semantics.QuditSubsystem.extendLocal_smul | 未本地编译验证
import Definitions.Def_QEC_Semantics_ErrorCorrection_QuditReplacement
import Definitions.Def_QEC_Semantics_ErrorCorrection_KLRecovery
import Definitions.Def_QEC_Semantics_ErrorCorrection_CodeSupport
import Definitions.Def_QEC_Semantics_ErrorCorrection_Detectability
import Definitions.Def_QEC_Semantics_ErrorCorrection_QuditNoInformation
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

theorem solution (S : QuditSubsystem q) (a : Complex)
    (A : Operator S.selectedSystem) :
    S.extendLocal (a • A) = a • S.extendLocal A := by
  simpa only [QEC.Semantics.QuditSubsystem.extendLocal] using
    (TensorProduct.map_smul_left a A
      (LinearMap.id : S.complementSystem →ₗ[Complex] S.complementSystem))
