-- Prove2me | solution 1 for ShiTM.initList_haltList_comp
-- status  : ACCEPTED   (prove)
-- author  : @Goku
-- created : 2026-09-14T21:44:49.239037+00:00
-- url     : https://prove2.me/submissions/847e68b1-2edb-4da0-8cdd-04bc814c277c

/-
Copyright (c) 2026 Yueheng Shi. All rights reserved.
Released under the Apache License, Version 2.0.
Authors: Yueheng Shi

`Turing.initList` / `Turing.haltList` for the sequential composite `ShiTM2.comp`.
-/
import Definitions.Def_ShiTM2_Composite
import Theorems.Thm_ShiTM_initList_haltList_laws

set_option autoImplicit false

open ShiTM2

/-! ### Disjointness of the three stack blocks of `CompK`

Only the three `≠` facts actually needed to feed the "every other key is empty" clauses of
`ShiTM.initList_haltList_laws` are proved here. -/

/-- `injK₁` is injective, in the contrapositive form the `dite` side conditions want. -/
private lemma shiInit_injK₁_ne (tm₁ tm₂ : Turing.FinTM2) (i j : tm₁.K) (h : i ≠ j) :
    injK₁ tm₁ tm₂ i ≠ injK₁ tm₁ tm₂ j := by
  intro he
  refine h ?_
  first
    | (exact Sum.inl_injective he)
    | (injection he with he'
       exact he')
    | (simpa using he)

/-- The second machine's stack block is disjoint from the first machine's. -/
private lemma shiInit_injK₂_ne_injK₁ (tm₁ tm₂ : Turing.FinTM2) (i : tm₂.K) (j : tm₁.K) :
    injK₂ tm₁ tm₂ i ≠ injK₁ tm₁ tm₂ j := by
  intro he
  first
    | (exact Sum.noConfusion he)
    | (simpa using he)
    | (cases he
       done)

/-- The scratch stack is not one of the first machine's stacks. -/
private lemma shiInit_kScr_ne_injK₁ (tm₁ tm₂ : Turing.FinTM2) (j : tm₁.K) :
    kScr tm₁ tm₂ ≠ injK₁ tm₁ tm₂ j := by
  intro he
  first
    | (exact Sum.noConfusion he)
    | (simpa using he)
    | (cases he
       done)

/-- **The `initList` / `haltList` boundary conditions of the sequential composite.**

For `comp tm₁ tm₂ tr dflt` the initial configuration has label `injΛ₁ tm₁ tm₂ tm₁.main`,
internal state `compInitialState tm₁ tm₂`, the input list on `injK₁ tm₁ tm₂ tm₁.k₀` and nothing
anywhere else; the final configuration has label `none`, the same internal state, the output list
on `injK₂ tm₁ tm₂ tm₂.k₁` and nothing anywhere else.

The last three conjuncts are the ones that make this usable downstream: restricted along the
first injection the composite's initial stacks are *literally* `tm₁`'s initial stacks (no cast:
`CompΓ tm₁ tm₂ (injK₁ tm₁ tm₂ i)` is `tm₁.Γ i` by `rfl`), while the second machine's stacks and
the scratch stack start empty. -/
theorem solution (tm₁ tm₂ : Turing.FinTM2) (tr : tm₁.Γ tm₁.k₁ → tm₂.Γ tm₂.k₀)
    (dflt : tm₂.Γ tm₂.k₀)
    (s : List ((comp tm₁ tm₂ tr dflt).Γ (comp tm₁ tm₂ tr dflt).k₀))
    (t : List ((comp tm₁ tm₂ tr dflt).Γ (comp tm₁ tm₂ tr dflt).k₁)) :
    (Turing.initList (comp tm₁ tm₂ tr dflt) s).l
        = Option.some (injΛ₁ tm₁ tm₂ tm₁.main)
      ∧ (Turing.initList (comp tm₁ tm₂ tr dflt) s).var = compInitialState tm₁ tm₂
      ∧ (Turing.initList (comp tm₁ tm₂ tr dflt) s).stk (injK₁ tm₁ tm₂ tm₁.k₀) = s
      ∧ (∀ k : CompK tm₁ tm₂, k ≠ injK₁ tm₁ tm₂ tm₁.k₀ →
          (Turing.initList (comp tm₁ tm₂ tr dflt) s).stk k = [])
      ∧ (Turing.haltList (comp tm₁ tm₂ tr dflt) t).l = Option.none
      ∧ (Turing.haltList (comp tm₁ tm₂ tr dflt) t).var = compInitialState tm₁ tm₂
      ∧ (Turing.haltList (comp tm₁ tm₂ tr dflt) t).stk (injK₂ tm₁ tm₂ tm₂.k₁) = t
      ∧ (∀ k : CompK tm₁ tm₂, k ≠ injK₂ tm₁ tm₂ tm₂.k₁ →
          (Turing.haltList (comp tm₁ tm₂ tr dflt) t).stk k = [])
      ∧ (∀ i : tm₁.K, (Turing.initList (comp tm₁ tm₂ tr dflt) s).stk (injK₁ tm₁ tm₂ i)
          = (Turing.initList tm₁ s).stk i)
      ∧ (∀ i : tm₂.K,
          (Turing.initList (comp tm₁ tm₂ tr dflt) s).stk (injK₂ tm₁ tm₂ i) = [])
      ∧ (Turing.initList (comp tm₁ tm₂ tr dflt) s).stk (kScr tm₁ tm₂) = [] := by
  obtain ⟨hl, hv, hk, hne, hhl, hhv, hhk, hhne⟩ :=
    ShiTM.initList_haltList_laws (comp tm₁ tm₂ tr dflt) s t
  obtain ⟨-, -, h1k, h1ne, -, -, -, -⟩ :=
    ShiTM.initList_haltList_laws tm₁ s ([] : List (tm₁.Γ tm₁.k₁))
  refine ⟨hl, hv, hk, hne, hhl, hhv, hhk, hhne, ?_, ?_, ?_⟩
  · intro i
    by_cases hi : i = tm₁.k₀
    · subst hi
      rw [h1k]
      exact hk
    · rw [hne (injK₁ tm₁ tm₂ i) (shiInit_injK₁_ne tm₁ tm₂ i tm₁.k₀ hi), h1ne i hi]
      -- `rw`'s closing `rfl` runs at REDUCIBLE transparency and cannot see
      -- `List (CompΓ tm₁ tm₂ (injK₁ tm₁ tm₂ i))` = `List (tm₁.Γ i)` through the
      -- semireducible `Sum.elim`, so the two `[]`s are left staring at each other.
      first
      | rfl
      | exact rfl
      | simp
  · intro i
    exact hne (injK₂ tm₁ tm₂ i) (shiInit_injK₂_ne_injK₁ tm₁ tm₂ i tm₁.k₀)
  · exact hne (kScr tm₁ tm₂) (shiInit_kScr_ne_injK₁ tm₁ tm₂ tm₁.k₀)
