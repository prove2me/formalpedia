-- Prove2me | solution 1 for QEC.Distillation.Ngu24MultiplicativeCSS.SourceInput.puncturedLogicalWord_pairing_eq_neg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T12:49:06.241365+00:00
-- url     : https://prove2.me/submissions/7de0d611-0aaf-42fd-9eeb-736d590bf072

import Definitions.Def_QEC_Coding_Core_Definitions
import Definitions.Def_QEC_Distillation_MultiplicativeQuditProtocol_Register
import Definitions.Def_QEC_Distillation_Core_TransversalGate
import Definitions.Def_QEC_Distillation_MultiplicativeQuditProtocol_CSSShortening
import Theorems.Thm_QEC_Distillation_Ngu24MultiplicativeCSS_SourceInput_systematicLogicalWord_mem_code
import Theorems.Thm_QEC_Distillation_Ngu24MultiplicativeCSS_SourceInput_shortenedCode_pairing
import Theorems.Thm_QEC_Distillation_Ngu24MultiplicativeCSS_SourceInput_wordPairing_partition
import Theorems.Thm_QEC_Distillation_EncodedCode_ImplementsLogicalGate_symm


set_option autoImplicit false
noncomputable section
open QEC QEC.Distillation QEC.Distillation.Ngu24MultiplicativeCSS
open Coding Semantics
open scoped BigOperators
universe u
variable {F I Logical : Type u} [Field F] [Fintype F] [Fintype I] [Fintype Logical]
attribute [local instance] QEC.Distillation.Ngu24MultiplicativeCSS._p2m_local_instance_7d0f4269de_23
attribute [local instance] QEC.Distillation.Ngu24MultiplicativeCSS._p2m_local_instance_7d0f4269de_24
attribute [local instance] QEC.Distillation.Ngu24MultiplicativeCSS._p2m_local_instance_7d0f4269de_25
open QEC.Distillation.Ngu24MultiplicativeCSS.SourceInput
namespace QEC.Distillation.Ngu24MultiplicativeCSS.SourceInput
theorem _root_.solution (data : SourceInput F I Logical)
    (u v : Word F Logical) :
    wordPairing (data.puncturedLogicalWord u) (data.puncturedLogicalWord v) =
      -wordPairing u v := by
  have hfull : wordPairing (data.systematicLogicalWord u)
      (data.systematicLogicalWord v) = 0 :=
    data.shortenedCode_pairing (data.systematicLogicalWord_mem_code u)
      (data.systematicLogicalWord_mem_code v)
  have hpartition := data.wordPairing_partition
    (data.systematicLogicalWord u) (data.systematicLogicalWord v)
  rw [data.pivotCoordinates_systematicLogicalWord,
    data.pivotCoordinates_systematicLogicalWord, hfull] at hpartition
  exact eq_neg_of_add_eq_zero_right hpartition.symm
end QEC.Distillation.Ngu24MultiplicativeCSS.SourceInput
