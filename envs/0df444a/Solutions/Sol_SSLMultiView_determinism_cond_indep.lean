-- Prove2me | solution 1 for SSLMultiView.determinism_cond_indep
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-25T22:02:39.497753+00:00
-- url     : https://prove2.me/submissions/cf05f39c-81ce-4856-9fbb-2c263cb8fc3e

import Mathlib
import Definitions.Def_SSLMultiView_Basic

set_option autoImplicit false

open Real

namespace S71CI
open SSLMultiView

lemma ci {Ω α β γ : Type*} [Fintype Ω] [DecidableEq α] [DecidableEq β] [DecidableEq γ]
    (P : Ω → ℝ) (f : Ω → α) (h : Ω → γ) (G : γ → β) :
    CondIndep P f (fun ω => G (h ω)) h := by
  intro a b c
  unfold law
  by_cases hb : G c = b
  · have e1 : Finset.univ.filter (fun ω => (f ω, G (h ω), h ω) = (a, b, c)) =
        Finset.univ.filter (fun ω => (f ω, h ω) = (a, c)) := by
      ext ω
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Prod.mk.injEq]
      constructor
      · rintro ⟨h1, _, h3⟩; exact ⟨h1, h3⟩
      · rintro ⟨h1, h3⟩; exact ⟨h1, by rw [h3, hb], h3⟩
    have e2 : Finset.univ.filter (fun ω => (G (h ω), h ω) = (b, c)) =
        Finset.univ.filter (fun ω => h ω = c) := by
      ext ω
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Prod.mk.injEq]
      constructor
      · rintro ⟨_, h3⟩; exact h3
      · intro h3; exact ⟨by rw [h3, hb], h3⟩
    rw [e1, e2]; ring
  · have e1 : Finset.univ.filter (fun ω => (f ω, G (h ω), h ω) = (a, b, c)) = ∅ := by
      ext ω
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Prod.mk.injEq,
        Finset.notMem_empty, iff_false, not_and]
      intro _ h2 h3; exact hb (by rw [← h3]; exact h2)
    have e2 : Finset.univ.filter (fun ω => (G (h ω), h ω) = (b, c)) = ∅ := by
      ext ω
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Prod.mk.injEq,
        Finset.notMem_empty, iff_false, not_and]
      intro h2 h3; exact hb (by rw [← h3]; exact h2)
    rw [e1, e2]; simp

end S71CI

open SSLMultiView S71CI in
theorem solution {X S T Zs : Type*} [Fintype X] [DecidableEq X] [Fintype S] [DecidableEq S]
    [Fintype T] [DecidableEq T] [Fintype Zs] [DecidableEq Zs]
    (P : X × S × T → ℝ) (hP : IsPMF P) (F : X → Zs) :
    CondIndep P taskT (rep F) inputX ∧ CondIndep P signalS (rep F) inputX ∧
      CondIndep P signalTask (rep F) inputX :=
  ⟨ci P taskT inputX F, ci P signalS inputX F, ci P signalTask inputX F⟩
