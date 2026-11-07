-- Prove2me | solution 1 for QEC.Distillation.Ngu24MultiplicativeCCZ.puncturedTriplePairing_eq_logical_delta_of_char_two
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T15:23:43.626401+00:00
-- url     : https://prove2.me/submissions/704f9f01-897b-460d-b2ce-5e15441b95d5

import Definitions.Def_QEC_Distillation_MultiplicativeQuditProtocol_CSSShortening
import Definitions.Def_QEC_Distillation_MultiplicativeQuditProtocol_PhysicalCCZ
import Definitions.Def_QEC_Distillation_MultiplicativeQuditProtocol_CCZIntertwining
import Theorems.Thm_QEC_Distillation_Ngu24MultiplicativeCCZ_logicalBasisTriplePairing_eq_delta

set_option autoImplicit false
noncomputable section
open QEC QEC.Distillation QEC.Distillation.Ngu24MultiplicativeCCZ
open Coding Semantics
open scoped BigOperators
open Ngu24MultiplicativeCSS
universe u
variable {F I Logical : Type u} [Field F] [Fintype F] [Algebra (ZMod 2) F]
  [Fintype I] [Fintype Logical]
attribute [local instance] QEC.Distillation.Ngu24MultiplicativeCCZ._p2m_local_instance_df646da45e_25
attribute [local instance] QEC.Distillation.Ngu24MultiplicativeCCZ._p2m_local_instance_df646da45e_26
omit [Algebra (ZMod 2) F]
namespace QEC.Distillation.Ngu24MultiplicativeCCZ
theorem _root_.solution
    (data : SourceInput F I Logical) [CharP F 2] (a b c : Logical)
    (h₁ h₂ h₃ : data.H0) :
    wordTriplePairing (data.shortenedCosetLabel (canonicalBasisWord (F := F) a) h₁)
      (data.shortenedCosetLabel (canonicalBasisWord (F := F) b) h₂)
      (data.shortenedCosetLabel (canonicalBasisWord (F := F) c) h₃) =
        if a = b ∧ b = c then 1 else 0 := by
  rw [puncturedTriplePairing_eq_logical_of_char_two data,
    logicalBasisTriplePairing_eq_delta]
end QEC.Distillation.Ngu24MultiplicativeCCZ
