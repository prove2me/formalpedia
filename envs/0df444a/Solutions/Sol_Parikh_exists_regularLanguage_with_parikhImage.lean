-- Prove2me | solution 1 for Parikh.exists_regularLanguage_with_parikhImage
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T09:56:50.541627+00:00
-- url     : https://prove2.me/submissions/8345e785-3cf0-4199-bdf6-cc6ac2e89c89

module
public import Definitions.Def_LeanPool_Parikh_ExecutableCompiler
public import Mathlib.Computability.DFA
public import Definitions.Def_LeanPool_Parikh_RegularRealization
public import Definitions.Def_LeanPool_Parikh_Statements
public import Definitions.Def_LeanPool_Parikh_Api
public import Theorems.Thm_Parikh_converse


set_option autoImplicit true
@[expose] public section
public section
open Parikh
namespace Parikh
theorem _root_.solution {T : Type*} [Finite T] [DecidableEq T]
    (X : Set (CountVector T)) (hX : IsSemilinearSet X) :
    ∃ R : Language T, R.IsRegular ∧ parikhImage R = X := converse X hX
end Parikh
