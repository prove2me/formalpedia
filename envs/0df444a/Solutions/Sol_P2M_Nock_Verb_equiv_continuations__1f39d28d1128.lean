-- Prove2me | solution 1 for P2M_Nock_Verb_equiv_continuations__1f39d28d1128
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:19:31.824622+00:00
-- url     : https://prove2.me/submissions/8bf94bc5-6748-4f20-97e4-29b4b9a03c22

module
public import Definitions.Def_LeanPool_PureNock_Verb
public import Batteries.Tactic.Alias
public import Definitions.Def_LeanPool_PureNock_Trace
public import Theorems.Thm_Nock_Verb_equiv_continuations

set_option autoImplicit true
@[expose] public section
public section
open Nock
open Nock.Verb
namespace Nock.Verb
theorem _root_.solution (Λ : Nat) (F : Verb) : FiniteΛ Λ F ↔ FiniteTransitionΛ Λ F :=
  and_congr (equiv_continuations F) Iff.rfl
end Nock.Verb
