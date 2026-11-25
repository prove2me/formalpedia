-- Prove2me | solution 1 for PretorsionImageClosed.isIndecomposableModule_of_forall_isCompl
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T03:44:59.945395+00:00
-- url     : https://prove2.me/submissions/a199f99d-9955-4e08-8844-67d250a3aa0b

module
public import Mathlib.RingTheory.FiniteLength
public import Mathlib.RingTheory.Nilpotent.Basic
public import Mathlib.RingTheory.SimpleModule.Basic
public import Definitions.Def_PretorsionImageClosed_Modules_LocalRingIdempotents
public import Definitions.Def_PretorsionImageClosed_Modules_IndecomposableModule

set_option autoImplicit true
@[expose] public section
public section
open PretorsionImageClosed
universe u v w
variable (A : Type u) (M : Type v) [Semiring A] [AddCommMonoid M] [Module A M]
variable {A M}
namespace PretorsionImageClosed
theorem _root_.solution [Nontrivial M]
    (h : ∀ N P : Submodule A M, IsCompl N P → N = ⊥ ∨ P = ⊥) :
    IsIndecomposableModule A M :=
  ⟨‹_›, h⟩
end PretorsionImageClosed
