-- Prove2me | solution 1 for QEC.Coding.PauliSymplectic.weight_binaryMul_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T12:27:39.914342+00:00
-- url     : https://prove2.me/submissions/ec269121-bb69-4d39-90d7-808aca9f66c9

import Definitions.Def_QEC_Coding_Core_Definitions
import Definitions.Def_QEC_Semantics_ErrorCorrection_CodeSupport
import Definitions.Def_QEC_Semantics_ErrorCorrection_KLRecovery
import Definitions.Def_QEC_Semantics_Channels_Kraus
import Definitions.Def_QEC_Semantics_Channels_KrausKnillLaflamme
import Definitions.Def_QEC_Semantics_Core_Qubit
import Definitions.Def_QEC_Coding_Stabilizer_PauliSemantics
import Theorems.Thm_QEC_Coding_PauliSymplectic_support_binaryMul_subset

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
theorem _root_.solution (P Q : Binary ι) :
    weight (binaryMul P Q) ≤ weight P + weight Q := by
  calc
    weight (binaryMul P Q) = (support (binaryMul P Q)).card := rfl
    _ ≤ (support P ∪ support Q).card :=
      Finset.card_le_card (support_binaryMul_subset P Q)
    _ ≤ (support P).card + (support Q).card :=
      Finset.card_union_le (support P) (support Q)
    _ = weight P + weight Q := rfl
end QEC.Coding.PauliSymplectic
