-- Prove2me | solution 1 for PretorsionImageClosed.IsIndecomposableModule.isNilpotent_or_bijective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T03:50:32.019773+00:00
-- url     : https://prove2.me/submissions/48bab610-417d-43db-976a-b84d4e1ec759

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
variable [IsNoetherian A M] [IsArtinian A M]
namespace PretorsionImageClosed
namespace IsIndecomposableModule
theorem _root_.solution
    (h : IsIndecomposableModule A M) (f : Module.End A M) :
    IsNilpotent f ∨ Function.Bijective f := by
  obtain ⟨n, hn⟩ :=
    Filter.eventually_atTop.mp (LinearMap.eventually_isCompl_ker_pow_range_pow f)
  have hcompl := hn (n + 1) (Nat.le_succ n)
  rcases h.eq_bot_or_eq_bot hcompl with hker | hrange
  · refine Or.inr ⟨?_, ?_⟩
    · have hinj : Function.Injective (f ^ (n + 1)) := LinearMap.ker_eq_bot.mp hker
      intro x y hxy
      refine hinj ?_
      have hpow : f ^ (n + 1) = f ^ n * f := pow_succ f n
      simp only [hpow, Module.End.mul_apply, hxy]
    · have htop : LinearMap.range (f ^ (n + 1)) = ⊤ := by
        have hsup := hcompl.sup_eq_top
        rwa [hker, bot_sup_eq] at hsup
      have hle : LinearMap.range (f ^ (n + 1)) ≤ LinearMap.range f := by
        rw [pow_succ' f n]
        exact LinearMap.range_comp_le_range _ _
      exact LinearMap.range_eq_top.mp (top_le_iff.mp (htop ▸ hle))
  · exact Or.inl ⟨n + 1, LinearMap.range_eq_bot.mp hrange⟩
end IsIndecomposableModule
end PretorsionImageClosed
