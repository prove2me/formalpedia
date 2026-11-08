-- Prove2me | solution 1 for QBFBackdoor.toCNF_spec
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T15:07:07.23339+00:00
-- url     : https://prove2.me/submissions/124905fb-e19f-432e-8a3b-7f0281f64419

import Mathlib
import Definitions.Def_QBFBackdoor_toCNF

open QBFBackdoor in
theorem solution {n : ℕ} (ϕ : List (QBFBackdoor.GAtom n)) :
    (∀ a : Fin n → Bool, QBFBackdoor.SatAll ϕ a ↔
      ∀ c ∈ QBFBackdoor.toCNF ϕ, ∃ l ∈ c, a l.1 = l.2) ∧
    (∀ c ∈ QBFBackdoor.toCNF ϕ, c.card ≤ 2 ∧ (c.filter (fun l => l.2 = true)).card ≤ 1) := by
  have hCl : ∀ (C : QBFBackdoor.GAtom n) (a : Fin n → Bool),
      C.Sat a ↔ ∀ c ∈ C.toClauses, ∃ l ∈ c, a l.1 = l.2 := by
    intro C a
    cases C with
    | unit x b => simp [QBFBackdoor.GAtom.Sat, QBFBackdoor.GAtom.toClauses]
    | eq x y =>
      simp only [QBFBackdoor.GAtom.Sat, QBFBackdoor.GAtom.toClauses, List.mem_cons,
        List.mem_singleton, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
        Finset.mem_insert, Finset.mem_singleton, or_and_right, exists_or, exists_eq_left]
      cases hx : a x <;> cases hy : a y <;> simp [hx, hy]
  constructor
  · intro a
    unfold QBFBackdoor.SatAll QBFBackdoor.toCNF
    constructor
    · intro h c hc
      obtain ⟨C, hC1, hc2⟩ := List.mem_flatMap.1 hc
      exact (hCl C a).1 (h C hC1) c hc2
    · intro h C hC1
      exact (hCl C a).2 (fun c hc => h c (List.mem_flatMap.2 ⟨C, hC1, hc⟩))
  · intro c hc
    unfold QBFBackdoor.toCNF at hc
    obtain ⟨C, _, hc2⟩ := List.mem_flatMap.1 hc
    cases C with
    | unit x b =>
      simp only [QBFBackdoor.GAtom.toClauses, List.mem_singleton] at hc2
      subst hc2
      exact ⟨by simp, (Finset.card_filter_le _ _).trans (by simp)⟩
    | eq x y =>
      simp only [QBFBackdoor.GAtom.toClauses, List.mem_cons, List.mem_singleton,
        List.not_mem_nil, or_false] at hc2
      rcases hc2 with rfl | rfl
      · refine ⟨(Finset.card_insert_le _ _).trans (by simp), ?_⟩
        refine (Finset.card_le_card (t := {(x, true)}) ?_).trans (by simp)
        intro l hl
        simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton] at hl ⊢
        rcases hl with ⟨rfl | rfl, h⟩
        · rfl
        · simp at h
      · refine ⟨(Finset.card_insert_le _ _).trans (by simp), ?_⟩
        refine (Finset.card_le_card (t := {(y, true)}) ?_).trans (by simp)
        intro l hl
        simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton] at hl ⊢
        rcases hl with ⟨rfl | rfl, h⟩
        · simp at h
        · rfl
