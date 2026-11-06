-- Prove2me | solution 1 for QEC.Coding.PauliSymplectic.binarySwapPhase_eq_of_commutes
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T12:29:17.429071+00:00
-- url     : https://prove2.me/submissions/c90b995a-4c24-4a80-be4b-cbd40ceaeac3

import Definitions.Def_QEC_Coding_Core_Definitions
import Definitions.Def_QEC_Semantics_ErrorCorrection_CodeSupport
import Definitions.Def_QEC_Semantics_ErrorCorrection_KLRecovery
import Definitions.Def_QEC_Semantics_Channels_Kraus
import Definitions.Def_QEC_Semantics_Channels_KrausKnillLaflamme
import Definitions.Def_QEC_Semantics_Core_Qubit
import Definitions.Def_QEC_Coding_Stabilizer_PauliSemantics
import Theorems.Thm_QEC_Coding_PauliSymplectic_binarySwapPhase_eq_of_symplecticForm_eq_zero

set_option autoImplicit false
noncomputable section
open QEC
open QEC.Coding
open Classical
open scoped BigOperators
universe u w
open QEC.Coding.PauliSymplectic
variable {ι : Type u} [Fintype ι]
variable [DecidableEq ι]
namespace QEC.Coding.PauliSymplectic
theorem _root_.solution (P Q : Binary ι)
    (h : Commutes P Q) :
    binarySwapPhase Q.vector.xPart P.vector.zPart =
      binarySwapPhase P.vector.xPart Q.vector.zPart :=
  binarySwapPhase_eq_of_symplecticForm_eq_zero P Q h
end QEC.Coding.PauliSymplectic
