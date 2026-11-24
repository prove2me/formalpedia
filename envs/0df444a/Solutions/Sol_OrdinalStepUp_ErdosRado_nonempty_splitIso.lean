-- Prove2me | solution 1 for OrdinalStepUp.ErdosRado.nonempty_splitIso
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T04:49:37.936854+00:00
-- url     : https://prove2.me/submissions/bec8cf83-9f79-4d41-b1da-2d7aab46d1e4

import Mathlib.SetTheory.Cardinal.EventuallyConst
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Finset.Sort
import Mathlib.Tactic.FinCases
import Definitions.Def_OrdinalStepUp_Solution

set_option autoImplicit true
open OrdinalStepUp OrdinalStepUp.ErdosRado
open Ordinal
universe u
variable {n r : ℕ} {α β κ μ θ : Ordinal} {a b c : SetOrd} {𝒜 ℬ 𝒞 : Set SetOrd}
  {V : Type u} {wo wo' : WellOrder} {x : wo.α}
namespace OrdinalStepUp.ErdosRado
theorem _root_.solution {𝒜 ℬ : Set wo.α} (hBA : ℬ ⊆ 𝒜)
    (hfinal : ∀ y ∈ ℬ, ∀ x ∈ 𝒜, wo.r y x → x ∈ ℬ) :
    Nonempty (Sum.Lex (Subrel wo.r (· ∈ 𝒜 \ ℬ)) (Subrel wo.r (· ∈ ℬ))
      ≃r Subrel wo.r (· ∈ 𝒜)) := by
  rcases ℬ.eq_empty_or_nonempty with rfl | ⟨y₀, hy₀⟩
  · -- nothing is removed, and the second summand is empty
    rw [Set.sdiff_empty]; exact ⟨RelIso.sumLexEmpty _ _⟩
  -- `m` is the least element of `ℬ`; this is the point we cut at.
  set m := wo.wo.wf.min ℬ ⟨y₀, hy₀⟩ with hm
  have hmB : m ∈ ℬ := wo.wo.wf.min_mem _ _
  -- Being outside `ℬ` is the same as lying below the cut: below by minimality
  -- of `m`, and above only if `hfinal` has already pulled the point into `ℬ`.
  have key {a} : a ∈ 𝒜 → (wo.r a m ↔ a ∉ ℬ) := fun haA =>
    ⟨fun h hB => wo.wo.wf.not_lt_min _ hB h,
     fun hnB => (trichotomous_of wo.r a m).resolve_right fun h =>
       hnB (h.elim (· ▸ hmB) (hfinal m hmB a haA))⟩
  set R := Subrel wo.r (· ∈ 𝒜) with hR
  set x : {a // a ∈ 𝒜} := ⟨m, hBA hmB⟩ with hx
  -- A predicate on `𝒜` that describes membership of some `𝒟 ⊆ 𝒜` cuts out `𝒟`.
  have cut {p : {a // a ∈ 𝒜} → Prop} {𝒟 : Set wo.α} (h𝒟 : 𝒟 ⊆ 𝒜)
      (hp : ∀ a (h : a ∈ 𝒜), p ⟨a, h⟩ ↔ a ∈ 𝒟) : Subrel R p ≃r Subrel wo.r (· ∈ 𝒟) :=
    ⟨⟨fun q => ⟨q.1.1, (hp _ q.1.2).1 q.2⟩, fun q => ⟨⟨q.1, h𝒟 q.2⟩, (hp _ (h𝒟 q.2)).2 q.2⟩,
      fun _ => rfl, fun _ => rfl⟩, Iff.rfl⟩
  -- `key` says exactly that below the cut is `𝒜 \ ℬ`, and at or above it is `ℬ`.
  have e1 : Subrel R (R · x) ≃r Subrel wo.r (· ∈ 𝒜 \ ℬ) :=
    cut Set.sdiff_subset fun _ h => ⟨fun hr => ⟨h, (key h).1 hr⟩, fun hd => (key h).2 hd.2⟩
  have e2 : Subrel R (¬ R · x) ≃r Subrel wo.r (· ∈ ℬ) :=
    cut hBA fun _ h => (not_congr (key h)).trans not_not
  -- and a well-order is the lexicographic sum of the two sides of any cut.
  classical
  exact ⟨(RelIso.sumLexCongr e1.symm e2.symm).trans (RelIso.sumLexComplLeft R x)⟩
end OrdinalStepUp.ErdosRado
