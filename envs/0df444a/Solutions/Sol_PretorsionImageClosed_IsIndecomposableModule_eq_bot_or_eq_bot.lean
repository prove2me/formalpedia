-- Prove2me | solution 1 for PretorsionImageClosed.IsIndecomposableModule.eq_bot_or_eq_bot
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T01:28:30.07642+00:00
-- url     : https://prove2.me/submissions/6f391cef-d6bc-4146-a71c-95c08097c10e

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
namespace IsIndecomposableModule
theorem _root_.solution
    (h : IsIndecomposableModule A M) {N P : Submodule A M}
    (hNP : IsCompl N P) : N = ⊥ ∨ P = ⊥ :=
  h.2 N P hNP
end IsIndecomposableModule
end PretorsionImageClosed
