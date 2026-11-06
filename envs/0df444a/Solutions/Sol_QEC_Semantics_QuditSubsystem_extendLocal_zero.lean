-- Prove2me | solution 1 for QEC.Semantics.QuditSubsystem.extendLocal_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T12:29:18.736038+00:00
-- url     : https://prove2.me/submissions/032b3e1e-0b1a-4185-8487-158f6351b6d4

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
theorem _root_.solution (S : QuditSubsystem q) :
    S.extendLocal (0 : Operator S.selectedSystem) = 0 := by
  unfold extendLocal
  rw [TensorProduct.map_zero_left]
end QEC.Semantics.QuditSubsystem
