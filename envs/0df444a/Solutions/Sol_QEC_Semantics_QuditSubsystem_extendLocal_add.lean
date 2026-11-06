-- Prove2me | solution 1 for QEC.Semantics.QuditSubsystem.extendLocal_add
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T12:29:18.069205+00:00
-- url     : https://prove2.me/submissions/6e3ec293-3abb-48db-a599-beb535cd38ad

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
theorem _root_.solution (S : QuditSubsystem q)
    (A B : Operator S.selectedSystem) :
    S.extendLocal (A + B) = S.extendLocal A + S.extendLocal B := by
  unfold extendLocal
  rw [TensorProduct.map_add_left]
end QEC.Semantics.QuditSubsystem
