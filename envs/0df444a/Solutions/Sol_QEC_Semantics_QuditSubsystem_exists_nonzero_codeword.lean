-- Prove2me | solution 1 for QEC.Semantics.QuditSubsystem.exists_nonzero_codeword
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T12:17:05.73886+00:00
-- url     : https://prove2.me/submissions/be09109f-37cc-41d3-a6b6-2b962bd203f0

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
theorem _root_.solution
    (C : QuantumCode (Qudit.QuditRegister q)) (hC : C.carrier ≠ ⊥) :
    ∃ x : Qudit.QuditRegister q, x ∈ C.carrier ∧ x ≠ 0 := by
  rcases Submodule.nonzero_mem_of_bot_lt (bot_lt_iff_ne_bot.mpr hC) with ⟨x, hx⟩
  exact ⟨x, x.property, fun hzero => hx (Subtype.ext hzero)⟩
end QEC.Semantics.QuditSubsystem
