-- Prove2me | solution 1 for Parikh.dfaGrammar_language
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T09:50:14.215115+00:00
-- url     : https://prove2.me/submissions/a02d4df8-590e-4ba5-93da-258be97dfed5

module
public import Mathlib.Computability.ContextFreeGrammar
public import Mathlib.Computability.DFA
public import Mathlib.Data.Fintype.Prod
public import Definitions.Def_LeanPool_Parikh_DFAGrammar
public import Theorems.Thm_Parikh_dfaGrammar_derives_iff

set_option autoImplicit true
@[expose] public section
public section
open Parikh
variable {T : Type*} {σ : Type} [Fintype T] [Fintype σ]
namespace Parikh
theorem _root_.solution (M : DFA T σ) : (dfaGrammar M).language = M.accepts := by
  ext w
  exact dfaGrammar_derives_iff M M.start w
end Parikh
