-- Prove2me | solution 1 for QEC.Distillation.Ngu24MultiplicativeCSS.SourceInput.puncturedLogicalWord_pairing_puncture_one_eq_sum_of_char_two
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T15:22:46.126763+00:00
-- url     : https://prove2.me/submissions/05e43f72-5311-42a3-a8c5-620cd0ef6931

import Definitions.Def_QEC_Coding_Core_Definitions
import Definitions.Def_QEC_Distillation_MultiplicativeQuditProtocol_Register
import Definitions.Def_QEC_Distillation_Core_TransversalGate
import Definitions.Def_QEC_Distillation_MultiplicativeQuditProtocol_CSSShortening
import Theorems.Thm_QEC_Distillation_Ngu24MultiplicativeCSS_SourceInput_puncturedLogicalWord_pairing_puncture_one_eq_neg_sum
import Theorems.Thm_QEC_Distillation_EncodedCode_ImplementsLogicalGate_symm

section
noncomputable section
namespace QEC.Distillation.Ngu24MultiplicativeCSS
open Coding Semantics
open scoped BigOperators
universe u
variable {F I Logical : Type u} [Field F] [Fintype F] [Fintype I] [Fintype Logical]
namespace SourceInput
omit [Fintype F] in
private theorem neg_eq_self_of_char_two [CharP F 2] (a : F) : -a = a := by
  apply (eq_neg_of_add_eq_zero_left ?_).symm
  have htwo : (2 : F) = 0 := CharP.cast_eq_zero F 2
  rw [← two_mul, htwo, zero_mul]
end SourceInput
end QEC.Distillation.Ngu24MultiplicativeCSS
end
end

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
theorem _root_.solution
    (data : SourceInput F I Logical) [CharP F 2] (u : Word F Logical) :
    wordPairing (data.puncturedLogicalWord u) (data.puncture (1 : Word F I)) =
      ∑ a : Logical, u a := by
  rw [data.puncturedLogicalWord_pairing_puncture_one_eq_neg_sum]
  exact neg_eq_self_of_char_two _
end QEC.Distillation.Ngu24MultiplicativeCSS.SourceInput
