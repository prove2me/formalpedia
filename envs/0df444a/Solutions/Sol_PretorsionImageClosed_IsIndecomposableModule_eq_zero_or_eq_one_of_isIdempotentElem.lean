-- Prove2me | solution 1 for PretorsionImageClosed.IsIndecomposableModule.eq_zero_or_eq_one_of_isIdempotentElem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T01:33:38.28633+00:00
-- url     : https://prove2.me/submissions/2ecd8cb9-7fcc-44e5-8d8d-fb15b7b11ef7

module
public import Mathlib.RingTheory.FiniteLength
public import Mathlib.RingTheory.Nilpotent.Basic
public import Mathlib.RingTheory.SimpleModule.Basic
public import Definitions.Def_PretorsionImageClosed_Modules_LocalRingIdempotents
public import Definitions.Def_PretorsionImageClosed_Modules_IndecomposableModule
public import Theorems.Thm_PretorsionImageClosed_IsIndecomposableModule_eq_bot_or_eq_bot

set_option autoImplicit true
@[expose] public section
public section
open PretorsionImageClosed
universe u v w
variable {A : Type u} {M : Type v} [Ring A] [AddCommGroup M] [Module A M]
namespace PretorsionImageClosed
namespace IsIndecomposableModule
theorem _root_.solution
    (h : IsIndecomposableModule A M) {f : Module.End A M}
    (hf : IsIdempotentElem f) : f = 0 ∨ f = 1 := by
  rcases h.eq_bot_or_eq_bot (LinearMap.IsIdempotentElem.isCompl hf) with hrange | hker
  · exact Or.inl (LinearMap.range_eq_bot.mp hrange)
  · refine Or.inr (LinearMap.ext fun x ↦ ?_)
    have hinj : Function.Injective f := LinearMap.ker_eq_bot.mp hker
    have hx : f (f x) = f x := DFunLike.congr_fun hf x
    simpa using hinj hx
end IsIndecomposableModule
end PretorsionImageClosed
