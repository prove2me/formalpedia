-- Prove2me | solution 1 for PretorsionImageClosed.IsIndecomposableModule.nontrivial
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T00:34:09.043865+00:00
-- url     : https://prove2.me/submissions/7f6914b2-638f-4dde-977b-0dc8ee274785

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
    (h : IsIndecomposableModule A M) : Nontrivial M :=
  h.1
end IsIndecomposableModule
end PretorsionImageClosed
