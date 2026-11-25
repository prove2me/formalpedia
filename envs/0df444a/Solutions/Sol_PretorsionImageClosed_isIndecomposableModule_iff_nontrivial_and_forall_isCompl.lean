-- Prove2me | solution 1 for PretorsionImageClosed.isIndecomposableModule_iff_nontrivial_and_forall_isCompl
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T05:18:21.33493+00:00
-- url     : https://prove2.me/submissions/2f793ae1-8311-4001-b406-8ff8e3fdb020

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
theorem _root_.solution :
    IsIndecomposableModule A M ↔
      Nontrivial M ∧ ∀ N P : Submodule A M, IsCompl N P → N = ⊥ ∨ P = ⊥ :=
  Iff.rfl
end PretorsionImageClosed
