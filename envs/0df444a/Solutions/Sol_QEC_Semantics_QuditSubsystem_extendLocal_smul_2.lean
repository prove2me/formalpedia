-- Prove2me | solution 2 for QEC.Semantics.QuditSubsystem.extendLocal_smul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T20:18:34.047808+00:00
-- url     : https://prove2.me/submissions/8e841002-c85a-4c9d-9c17-89f9b9dfe314

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
namespace QEC.Semantics.QuditSubsystem
theorem _root_.solution (S : QuditSubsystem q) (a : Complex)
    (A : Operator S.selectedSystem) :
    S.extendLocal (a • A) = a • S.extendLocal A := by
  unfold extendLocal
  rw [TensorProduct.map_smul_left]
end QEC.Semantics.QuditSubsystem
