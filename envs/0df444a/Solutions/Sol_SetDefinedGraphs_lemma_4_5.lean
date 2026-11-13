-- Prove2me | solution 1 for SetDefinedGraphs.lemma_4_5
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T08:21:50.752614+00:00
-- url     : https://prove2.me/submissions/039a358d-cec6-445f-bab7-a37c66161cbd

import Mathlib
import Definitions.Def_SetDefinedGraphs_realisation
import Definitions.Def_SetDefinedGraphs_VectorSets
import Definitions.Def_SetDefinedGraphs_Clauses
import Definitions.Def_SetDefinedGraphs_Classes

section
set_option autoImplicit false
namespace SetDefinedGraphs.Dev.Cyc
open SetDefinedGraphs

theorem core {d : ℕ} (C : FullClause (Fin d)) (hC : IsCyclicClause C) (V : Set (Fin d → ℕ))
    (hV : IsInjectiveSet V) (hO : IsOrderUniform V) (u w : Fin d → ℕ) (hu : u ∈ V) (hw : w ∈ V) :
    eqPattern u w ≠ C := by
  intro h
  obtain ⟨_, k, hk, x, hx, hxC⟩ := hC
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  have hrot : ∀ t : Fin (m+1), finRotate (m+1) t = t + 1 := fun t => finRotate_succ_apply t
  have heq : ∀ t : Fin (m+1), u (x t) = w (x (t+1)) := by
    intro t
    have := congrFun (congrFun h (x t)) (x (finRotate (m+1) t))
    rw [hxC t] at this
    rw [← hrot]
    simpa [eqPattern] using this
  set a : Fin (m+1) → ℕ := fun t => u (x t) with ha
  have hainj : Function.Injective a := (hV u hu).comp hx
  have hd : ∀ t : Fin (m+1), a t < a (t+1) ↔ a (t+1) < a (t+1+1) := by
    intro t
    have := hO u hu w hw (x (t+1)) (x (t+1+1))
    have e1 : w (x (t+1)) = a t := (heq t).symm
    have e2 : w (x (t+1+1)) = a (t+1) := (heq (t+1)).symm
    rw [e1, e2] at this
    exact this.symm
  have hconst : ∀ n : ℕ, ∀ hn : n < m + 1,
      (a ⟨n, hn⟩ < a (⟨n, hn⟩ + 1)) ↔ (a 0 < a (0+1)) := by
    intro n
    induction n with
    | zero => intro hn; rfl
    | succ n ih =>
      intro hn
      have e : (⟨n+1, hn⟩ : Fin (m+1)) = ⟨n, by omega⟩ + 1 := by
        apply Fin.ext
        rw [Fin.val_add_one_of_lt (by simp [Fin.lt_def]; omega)]
      rw [e, ← ih (by omega)]
      exact (hd _).symm
  have hall : ∀ t : Fin (m+1), (a t < a (t+1)) ↔ (a 0 < a (0+1)) := fun t => hconst t.val t.2
  obtain ⟨t1, -, h1⟩ := Finset.exists_min_image Finset.univ a ⟨0, by simp⟩
  obtain ⟨t0, -, h0⟩ := Finset.exists_max_image Finset.univ a ⟨0, by simp⟩
  have hne : ∀ t : Fin (m+1), a t ≠ a (t+1) := by
    intro t ht
    have := hainj ht
    have h2 : (2 : ℕ) ≤ m + 1 := hk
    have : (1 : Fin (m+1)) = 0 := by simpa using this
    have := congrArg Fin.val this
    rw [Fin.val_one', Fin.val_zero] at this
    have : (1 : ℕ) % (m+1) = 1 := Nat.mod_eq_of_lt (by omega)
    omega
  have hlt1 : a t1 < a (t1+1) := lt_of_le_of_ne (h1 _ (by simp)) (hne t1)
  have hlt0 : a (t0+1) < a t0 := lt_of_le_of_ne (h0 _ (by simp)) (fun e => hne t0 e.symm)
  have := (hall t1).1 hlt1
  have h3 := (hall t0).2 this
  exact absurd hlt0 (not_lt.2 h3.le)
end SetDefinedGraphs.Dev.Cyc
end

section
set_option autoImplicit false
namespace SetDefinedGraphs
open SetDefinedGraphs.Dev.Cyc in
theorem chk_lemma_4_5 {d : ℕ} (C : FullClause (Fin d)) (hC : IsCyclicClause C) {W : Type} (G : Digraph W)
    (hG : InY (dnfFun {C}) G) : ∀ a b, ¬ G.Adj a b := by
  obtain ⟨V, -, hinj, hou, e, he⟩ := hG
  intro a b hab
  have := ((he a b).1 hab).2
  have h2 : eqPattern (e a).1 (e b).1 = C := by
    simpa [dnfFun] using this
  exact core C hC V hinj hou _ _ (e a).2 (e b).2 h2
end SetDefinedGraphs
end

theorem solution : type_of% @SetDefinedGraphs.chk_lemma_4_5 := @SetDefinedGraphs.chk_lemma_4_5
