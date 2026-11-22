-- Prove2me | solution 1 for Parikh.dfaGrammar_derives_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T09:48:07.120644+00:00
-- url     : https://prove2.me/submissions/94062d1d-c12e-4144-ac13-5ecab5ed979a

module
public import Mathlib.Computability.ContextFreeGrammar
public import Mathlib.Computability.DFA
public import Mathlib.Data.Fintype.Prod
public import Definitions.Def_LeanPool_Parikh_DFAGrammar

set_option autoImplicit true
@[expose] public section
public section
open Parikh
variable {T : Type*} {σ : Type} [Fintype T] [Fintype σ]
namespace Parikh
theorem _root_.solution (M : DFA T σ) (q : σ) (w : List T) :
    (dfaGrammar M).Derives [.nonterminal q] (w.map .terminal) ↔
      M.evalFrom q w ∈ M.accept := by
  classical
  have hrules (r : ContextFreeRule T σ) : r ∈ (dfaGrammar M).rules ↔
      (∃ s a, r = ⟨s, [.terminal a, .nonterminal (M.step s a)]⟩) ∨
      (∃ s, s ∈ M.accept ∧ r = ⟨s, []⟩) := by
    dsimp only [dfaGrammar]
    simp only [Finset.mem_union, Finset.mem_image, Finset.mem_univ,
      Finset.mem_filter, true_and]
    constructor
    · rintro (⟨⟨s, a⟩, hr⟩ | ⟨s, hs, hr⟩)
      · exact Or.inl ⟨s, a, hr.symm⟩
      · exact Or.inr ⟨s, hs, hr.symm⟩
    · rintro (⟨s, a, rfl⟩ | ⟨s, hs, rfl⟩)
      · exact Or.inl ⟨(s, a), rfl⟩
      · exact Or.inr ⟨s, hs, rfl⟩
  have hrewrite (r : ContextFreeRule T σ) (u : List T) (s : σ)
      (v : List (Symbol T σ))
      (h : r.Rewrites (u.map .terminal ++ [.nonterminal s]) v) :
      r.input = s ∧ v = u.map .terminal ++ r.output := by
    induction u generalizing v with
    | nil =>
      cases h with
      | head => simp
      | cons _ h => cases h
    | cons a u ih =>
      cases h with
      | cons _ h =>
        obtain ⟨hs, hv⟩ := ih _ h
        exact ⟨hs, by simp [hv]⟩
  have hterminal (u : List T) (v : List (Symbol T σ)) :
      ¬ (dfaGrammar M).Produces (u.map .terminal) v := by
    rintro ⟨r, _, hr⟩
    have := hr.nonterminal_input_mem
    simp at this
  constructor
  · intro h
    have hinvariant {v : List (Symbol T σ)}
        (hv : (dfaGrammar M).Derives [.nonterminal q] v) :
        (∃ u, v = u.map .terminal ∧ M.evalFrom q u ∈ M.accept) ∨
        (∃ u s, v = u.map .terminal ++ [.nonterminal s] ∧ M.evalFrom q u = s) := by
      induction hv with
      | refl => exact Or.inr ⟨[], q, rfl, rfl⟩
      | tail _ hstep ih =>
        rcases ih with ⟨u, rfl, _⟩ | ⟨u, s, rfl, hrun⟩
        · exact (hterminal _ _ hstep).elim
        · obtain ⟨r, hr, hrewriteStep⟩ := hstep
          obtain ⟨hinput, rfl⟩ := hrewrite r u s _ hrewriteStep
          rcases (hrules r).mp hr with ⟨s', a, rfl⟩ | ⟨s', hs', rfl⟩
          · change s' = s at hinput
            subst s'
            right
            refine ⟨u ++ [a], M.step s a, ?_, ?_⟩
            · simp
            · simp [DFA.evalFrom_of_append, hrun]
          · change s' = s at hinput
            subst s'
            left
            exact ⟨u, by simp, hrun ▸ hs'⟩
    rcases hinvariant h with ⟨u, hu, haccept⟩ | ⟨u, s, hu, _⟩
    · have : w = u := (List.map_inj_right (fun _ _ h => Symbol.terminal.inj h)).mp hu
      simpa [this] using haccept
    · have : (.nonterminal s : Symbol T σ) ∈ w.map .terminal := by
        exact hu.symm ▸ (by simp)
      simp at this
  · intro h
    induction w generalizing q with
    | nil =>
      apply ContextFreeGrammar.Produces.single
      refine ⟨⟨q, []⟩, (hrules _).mpr (Or.inr ⟨q, h, rfl⟩), ?_⟩
      exact ContextFreeRule.Rewrites.input_output
    | cons a w ih =>
      have hstep : (dfaGrammar M).Produces [.nonterminal q]
          [.terminal a, .nonterminal (M.step q a)] :=
        ⟨⟨q, [.terminal a, .nonterminal (M.step q a)]⟩,
          (hrules _).mpr (Or.inl ⟨q, a, rfl⟩), ContextFreeRule.Rewrites.input_output⟩
      exact hstep.trans_derives ((ih (M.step q a) h).append_left [.terminal a])
end Parikh
