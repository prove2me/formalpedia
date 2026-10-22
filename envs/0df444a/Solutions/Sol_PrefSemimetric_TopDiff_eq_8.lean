-- Prove2me | solution 1 for PrefSemimetric.TopDiff.eq_8
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung
-- created : 2026-10-21T16:59:53.612982+00:00
-- url     : https://prove2.me/submissions/ac97addb-f6a6-42c4-9609-52c115ebadc6

import Mathlib
import Definitions.Def_PrefSemimetric_TopDiff_Model

open PrefSemimetric.TopDiff

theorem ps_acyclic_of_rank {X : Type*} (R : X → X → Prop) (hrefl : ∀ x, R x x)
    (f : X → ℕ) (hf : ∀ x y, asymmPart R x y → f x < f y) : IsAcyclicOrder R := by
  refine ⟨hrefl, ?_⟩
  intro x hx
  have key : ∀ y z, Relation.TransGen (asymmPart R) y z → f y < f z := by
    intro y z h
    induction h with
    | single h => exact hf _ _ h
    | tail _ h ih => exact lt_trans ih (hf _ _ h)
  exact lt_irrefl _ (key x x hx)

theorem ps_asymm_AB {X : Type*} (a b : X) (hab : a ≠ b) (y x : X) :
    asymmPart (prefAB a b) y x ↔ (y ≠ a ∧ y ≠ b ∧ (x = a ∨ x = b)) := by
  simp only [asymmPart, prefAB]
  by_cases h1 : y = a <;> by_cases h2 : y = b <;> by_cases h3 : x = a <;> by_cases h4 : x = b <;>
    simp_all [eq_comm]

theorem ps_asymm_ABplus {X : Type*} (a b : X) (hab : a ≠ b) (y x : X) :
    asymmPart (prefABplus a b) y x ↔ ((y ≠ a ∧ y ≠ b ∧ (x = a ∨ x = b)) ∨ (y = a ∧ x = b)) := by
  simp only [asymmPart, prefABplus, prefAB]
  by_cases h1 : y = a <;> by_cases h2 : y = b <;> by_cases h3 : x = a <;> by_cases h4 : x = b <;>
    simp_all [eq_comm]

theorem solution {X : Type*} [Fintype X] [DecidableEq X]
    (w : X → ℝ) (hw : ∀ x, 0 ≤ w x) (a b : X) (hab : a ≠ b) :
    IsAcyclicOrder (prefAB a b) ∧ IsAcyclicOrder (prefABplus a b) ∧
      Dmu w (prefAB a b) (prefABplus a b) = w b := by
  classical
  let f : X → ℕ := fun x => if x = b then 2 else if x = a then 1 else 0
  refine ⟨?_, ?_, ?_⟩
  · apply ps_acyclic_of_rank (prefAB a b) (fun x => Or.inl rfl) f
    intro y x h
    rw [ps_asymm_AB a b hab] at h
    obtain ⟨h1, h2, h3⟩ := h
    rcases h3 with rfl | rfl <;> simp [f, h1, h2, hab, Ne.symm hab]
  · apply ps_acyclic_of_rank (prefABplus a b) (fun x => Or.inl (Or.inl rfl)) f
    intro y x h
    rw [ps_asymm_ABplus a b hab] at h
    rcases h with ⟨h1, h2, h3⟩ | ⟨rfl, rfl⟩
    · rcases h3 with rfl | rfl <;> simp [f, h1, h2, hab, Ne.symm hab]
    · simp [f, hab, Ne.symm hab]
  · have hdiff : ∀ S : Finset X, symmDiff (maxSet S (prefAB a b)) (maxSet S (prefABplus a b)) =
        if S = {a, b} then {b} else ∅ := by
      intro S
      have hSab : S = {a, b} ↔ (a ∈ S ∧ b ∈ S ∧ ∀ y ∈ S, y = a ∨ y = b) := by
        constructor
        · rintro rfl; simp
        · rintro ⟨ha, hb, hall⟩
          ext y; simp only [Finset.mem_insert, Finset.mem_singleton]
          constructor
          · exact hall y
          · rintro (rfl | rfl) <;> assumption
      ext x
      simp only [Finset.mem_symmDiff, maxSet, Finset.mem_filter, ps_asymm_AB a b hab,
        ps_asymm_ABplus a b hab]
      split_ifs with hS
      · rw [hSab] at hS
        obtain ⟨ha, hb, hall⟩ := hS
        simp only [Finset.mem_singleton]
        constructor
        · rintro (⟨⟨hx, h⟩, hn⟩ | ⟨⟨hx, h⟩, hn⟩)
          · by_contra hxb
            apply hn
            refine ⟨hx, fun y hy hc => ?_⟩
            rcases hc with ⟨h1, h2, h3⟩ | ⟨h1, h2⟩
            · rcases hall y hy with h' | h' <;> simp_all
            · exact hxb h2
          · exfalso; apply hn; refine ⟨hx, fun y hy hc => h y hy (Or.inl hc)⟩
        · rintro rfl
          left
          refine ⟨⟨hb, fun y hy hc => ?_⟩, fun hc => ?_⟩
          · rcases hall y hy with h' | h' <;> simp_all
          · exact hc.2 a ha (Or.inr ⟨rfl, rfl⟩)
      · rw [hSab] at hS
        simp only [Finset.notMem_empty, iff_false]
        rintro (⟨⟨hx, h⟩, hn⟩ | ⟨⟨hx, h⟩, hn⟩)
        · apply hn
          refine ⟨hx, fun y hy hc => ?_⟩
          rcases hc with hc | ⟨rfl, rfl⟩
          · exact h y hy hc
          · apply hS
            refine ⟨hy, hx, fun z hz => ?_⟩
            by_contra hzab
            push_neg at hzab
            exact h z hz ⟨hzab.1, hzab.2, Or.inr rfl⟩
        · exact hn ⟨hx, fun y hy hc => h y hy (Or.inl hc)⟩
    unfold Dmu
    simp only [hdiff]
    rw [Finset.sum_eq_single ({a, b} : Finset X)]
    · simp
    · intro S _ hS; simp [hS]
    · intro h; exact absurd (Finset.mem_univ _) h
