-- Prove2me | solution 1 for QEC.Coding.PauliSymplectic.binaryCSSQuantumCodeOfDualLe_finrank_carrier
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T12:29:37.611403+00:00
-- url     : https://prove2.me/submissions/dd0d4b33-acee-4715-b163-3575edd4122c

import Definitions.Def_QEC_Coding_Core_Definitions
import Definitions.Def_QEC_Semantics_ErrorCorrection_CodeSupport
import Definitions.Def_QEC_Semantics_ErrorCorrection_KLRecovery
import Definitions.Def_QEC_Semantics_Channels_Kraus
import Definitions.Def_QEC_Semantics_Channels_KrausKnillLaflamme
import Definitions.Def_QEC_Semantics_Core_Qubit
import Definitions.Def_QEC_Coding_Stabilizer_PauliSemantics
import Theorems.Thm_QEC_Coding_PauliSymplectic_finrank_binaryCSSLogicalBasisQuotient_eq

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
theorem _root_.solution
    (xCode zCode : LinearCode (ZMod 2) ι)
    (hdual : zCode.carrier ≤ xCode.dual.carrier) :
    Module.finrank Complex
      (binaryCSSQuantumCodeOfDualLe xCode zCode hdual).carrier =
    2 ^ (Length (ZMod 2) ι - Dimension xCode - Dimension zCode) := by
  rw [(binaryCSSQuantumCodeOfDualLeCarrierEquivLogicalBasisQuotient
    xCode zCode hdual).finrank_eq]
  rw [finrank_euclideanSpace]
  rw [Module.card_eq_pow_finrank
    (K := ZMod 2) (V := binaryCSSLogicalBasisQuotient xCode zCode)]
  rw [finrank_binaryCSSLogicalBasisQuotient_eq xCode zCode hdual]
  norm_num [ZMod.card]
end QEC.Coding.PauliSymplectic
