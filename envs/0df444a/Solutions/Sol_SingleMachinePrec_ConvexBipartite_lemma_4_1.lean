-- Prove2me | solution 1 for SingleMachinePrec.ConvexBipartite.lemma_4_1
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-07T02:29:10.312983+00:00
-- url     : https://prove2.me/submissions/c12f42c9-8119-4f28-b822-8b7ae06597f6

import Mathlib
import Definitions.Def_SingleMachinePrec_ConvexBipartite_ConvexBipartiteOrder

set_option autoImplicit false

namespace CBRealizerDa06

open SingleMachinePrec.ConvexBipartite SingleMachinePrec.Framework

/-- The linear order pulled back from a key into `ℤ ×ₗ ℤ`. -/
def R {N : Type} (f : N → Lex (ℤ × ℤ)) : N → N → Prop := fun x y => f x ≤ f y

theorem R_linear {N : Type} (f : N → Lex (ℤ × ℤ)) (hf : Function.Injective f) :
    IsLinearOrder N (R f) where
  refl x := le_refl (f x)
  trans _ _ _ h1 h2 := le_trans h1 h2
  antisymm _ _ h1 h2 := hf (le_antisymm h1 h2)
  total x y := le_total (f x) (f y)

theorem lex_lt {p q r s : ℤ} (h : p < r ∨ p = r ∧ q < s) :
    toLex (p, q) < toLex (r, s) :=
  Prod.Lex.toLex_lt_toLex.mpr h

theorem lex_eq {p q r s : ℤ} (h : (toLex (p, q) : Lex (ℤ × ℤ)) = toLex (r, s)) :
    p = r ∧ q = s := by
  have h' := congrArg ofLex h
  simpa using h'

theorem rev_of_lt {N : Type} (f : N → Lex (ℤ × ℤ)) {x y : N} (h : f y < f x) :
    Reverses (R f) x y :=
  ⟨le_of_lt h, fun e => by subst e; exact lt_irrefl _ h⟩

variable {a b : ℕ}

/-- `L₁`: all minus jobs ascending, then plus jobs by decreasing interval length, then
decreasing index. -/
def k0 (C : ConvexBipartiteOrder a b) : Job a b → Lex (ℤ × ℤ)
  | Sum.inl i => toLex (-(a : ℤ) - 1, ((i : ℕ) : ℤ))
  | Sum.inr k => toLex (-(((C.r k : ℕ) : ℤ) - ((C.l k : ℕ) : ℤ)), -((k : ℕ) : ℤ))

/-- `L₂`: minus jobs ascending, plus job `k` right after `r k`. -/
def k1 (C : ConvexBipartiteOrder a b) : Job a b → Lex (ℤ × ℤ)
  | Sum.inl i => toLex (2 * ((i : ℕ) : ℤ), 0)
  | Sum.inr k => toLex (2 * ((C.r k : ℕ) : ℤ) + 1, ((k : ℕ) : ℤ))

/-- `L₃`: minus jobs descending, plus job `k` right after `l k`. -/
def k2 (C : ConvexBipartiteOrder a b) : Job a b → Lex (ℤ × ℤ)
  | Sum.inl i => toLex (-2 * ((i : ℕ) : ℤ), 0)
  | Sum.inr k => toLex (-2 * ((C.l k : ℕ) : ℤ) + 1, ((k : ℕ) : ℤ))

theorem k0_inj (C : ConvexBipartiteOrder a b) : Function.Injective (k0 C) := by
  intro x y h
  rcases x with i | k <;> rcases y with j | k' <;> simp only [k0] at h <;>
    have h2 := lex_eq h
  · exact congrArg Sum.inl (Fin.ext (by omega))
  · have := (C.r k').isLt; omega
  · have := (C.r k).isLt; omega
  · exact congrArg Sum.inr (Fin.ext (by omega))

theorem k1_inj (C : ConvexBipartiteOrder a b) : Function.Injective (k1 C) := by
  intro x y h
  rcases x with i | k <;> rcases y with j | k' <;> simp only [k1] at h <;>
    have h2 := lex_eq h
  · exact congrArg Sum.inl (Fin.ext (by omega))
  · omega
  · omega
  · exact congrArg Sum.inr (Fin.ext (by omega))

theorem k2_inj (C : ConvexBipartiteOrder a b) : Function.Injective (k2 C) := by
  intro x y h
  rcases x with i | k <;> rcases y with j | k' <;> simp only [k2] at h <;>
    have h2 := lex_eq h
  · exact congrArg Sum.inl (Fin.ext (by omega))
  · omega
  · omega
  · exact congrArg Sum.inr (Fin.ext (by omega))

theorem prec_cases (C : ConvexBipartiteOrder a b) {x y : Job a b} (h : C.prec x y) :
    x = y ∨ ∃ i k, x = Sum.inl i ∧ y = Sum.inr k ∧
      (C.l k : ℕ) ≤ i ∧ (i : ℕ) ≤ C.r k := by
  rcases h with h | ⟨i, k, h1, h2, h3, h4⟩
  · exact Or.inl h
  · exact Or.inr ⟨i, k, h1, h2, h3, h4⟩

theorem k0_ext (C : ConvexBipartiteOrder a b) : ∀ x y, C.prec x y → R (k0 C) x y := by
  intro x y h
  rcases prec_cases C h with rfl | ⟨i, k, rfl, rfl, h1, h2⟩
  · exact le_refl _
  · have := (C.r k).isLt
    exact le_of_lt (lex_lt (Or.inl (by omega)))

theorem k1_ext (C : ConvexBipartiteOrder a b) : ∀ x y, C.prec x y → R (k1 C) x y := by
  intro x y h
  rcases prec_cases C h with rfl | ⟨i, k, rfl, rfl, h1, h2⟩
  · exact le_refl _
  · exact le_of_lt (lex_lt (Or.inl (by omega)))

theorem k2_ext (C : ConvexBipartiteOrder a b) : ∀ x y, C.prec x y → R (k2 C) x y := by
  intro x y h
  rcases prec_cases C h with rfl | ⟨i, k, rfl, rfl, h1, h2⟩
  · exact le_refl _
  · exact le_of_lt (lex_lt (Or.inl (by omega)))

theorem realizer (C : ConvexBipartiteOrder a b) :
    IsRealizer C.prec ![R (k0 C), R (k1 C), R (k2 C)] := by
  refine ⟨?_, ?_⟩
  · intro m
    fin_cases m
    · exact ⟨R_linear _ (k0_inj C), k0_ext C⟩
    · exact ⟨R_linear _ (k1_inj C), k1_ext C⟩
    · exact ⟨R_linear _ (k2_inj C), k2_ext C⟩
  · intro x y hinc
    obtain ⟨hxy, hyx⟩ := hinc
    rcases x with i | k <;> rcases y with j | k'
    · -- two minus jobs
      have hne : (i : ℕ) ≠ j := fun e => hxy (Or.inl (congrArg Sum.inl (Fin.ext e)))
      rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
      · exact ⟨2, rev_of_lt (k2 C) (lex_lt (Or.inl (by omega)))⟩
      · exact ⟨0, rev_of_lt (k0 C) (lex_lt (Or.inr ⟨rfl, by omega⟩))⟩
    · -- minus `i`, plus `k'`: need `k' < i`
      have hn : ¬ ((C.l k' : ℕ) ≤ i ∧ (i : ℕ) ≤ C.r k') := fun h =>
        hxy (Or.inr ⟨i, k', rfl, rfl, h.1, h.2⟩)
      by_cases hr : (i : ℕ) ≤ C.r k'
      · exact ⟨2, rev_of_lt (k2 C) (lex_lt (Or.inl (by omega)))⟩
      · exact ⟨1, rev_of_lt (k1 C) (lex_lt (Or.inl (by omega)))⟩
    · -- plus `k`, minus `j`: `L₁` puts every minus job first
      have := (C.r k).isLt
      exact ⟨0, rev_of_lt (k0 C) (lex_lt (Or.inl (by omega)))⟩
    · -- two plus jobs
      have hne : (k : ℕ) ≠ k' := fun e => hxy (Or.inl (congrArg Sum.inr (Fin.ext e)))
      have key :
          ((-(((C.r k' : ℕ) : ℤ) - ((C.l k' : ℕ) : ℤ)) < -(((C.r k : ℕ) : ℤ) - ((C.l k : ℕ) : ℤ)))
            ∨ (-(((C.r k' : ℕ) : ℤ) - ((C.l k' : ℕ) : ℤ)) = -(((C.r k : ℕ) : ℤ) - ((C.l k : ℕ) : ℤ))
              ∧ -((k' : ℕ) : ℤ) < -((k : ℕ) : ℤ))) ∨
          ((2 * ((C.r k' : ℕ) : ℤ) + 1 < 2 * ((C.r k : ℕ) : ℤ) + 1)
            ∨ (2 * ((C.r k' : ℕ) : ℤ) + 1 = 2 * ((C.r k : ℕ) : ℤ) + 1
              ∧ ((k' : ℕ) : ℤ) < ((k : ℕ) : ℤ))) ∨
          ((-2 * ((C.l k' : ℕ) : ℤ) + 1 < -2 * ((C.l k : ℕ) : ℤ) + 1)
            ∨ (-2 * ((C.l k' : ℕ) : ℤ) + 1 = -2 * ((C.l k : ℕ) : ℤ) + 1
              ∧ ((k' : ℕ) : ℤ) < ((k : ℕ) : ℤ))) := by
        omega
      rcases key with h | h | h
      · exact ⟨0, rev_of_lt (k0 C) (lex_lt h)⟩
      · exact ⟨1, rev_of_lt (k1 C) (lex_lt h)⟩
      · exact ⟨2, rev_of_lt (k2 C) (lex_lt h)⟩

end CBRealizerDa06

open SingleMachinePrec.ConvexBipartite in
theorem solution {a b : ℕ} (C : ConvexBipartiteOrder a b) :
    ∃ L : Fin 3 → Job a b → Job a b → Prop, IsRealizer C.prec L := by
  exact ⟨_, CBRealizerDa06.realizer C⟩
