-- Prove2me | solution 1 for SponsoredAssort.equation_1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-08T08:45:21.495302+00:00
-- url     : https://prove2.me/submissions/3f574998-affb-485f-9ef5-17c2272ffd4f

import Mathlib
import Definitions.Def_SponsoredAssort_IsIC
import Definitions.Def_SponsoredAssort_supp

open scoped NNReal

open SponsoredAssort in
theorem solution {n : ℕ} (r : Fin n → ℝ) (m : Mechanism n) (hIC : IsIC r m) (v : Attr n)
    (i : Fin n) :
    ∃ p : Finset (Fin n) → ℝ,
      (∀ y : ℝ≥0, m.pay (Function.update v i y) i = p (m.alloc (Function.update v i y))) ∧
      ∀ y : ℝ≥0, ∀ T ∈ supp m i v,
        r i * choiceProb T (Function.update v i y) i - p T ≤
          r i * choiceProb (m.alloc (Function.update v i y)) (Function.update v i y) i -
            p (m.alloc (Function.update v i y)) := by
  classical
  have hIC2 : ∀ y y' : ℝ≥0,
      r i * choiceProb (m.alloc (Function.update v i y')) (Function.update v i y) i -
          m.pay (Function.update v i y') i ≤
        r i * choiceProb (m.alloc (Function.update v i y)) (Function.update v i y) i -
          m.pay (Function.update v i y) i := by
    intro y y'
    have := hIC i (Function.update v i y) y'
    unfold utility at this
    simpa only [Function.update_idem, Function.update_self] using this
  have hpay : ∀ y y' : ℝ≥0, m.alloc (Function.update v i y) = m.alloc (Function.update v i y') →
      m.pay (Function.update v i y) i = m.pay (Function.update v i y') i := by
    intro y y' h
    have h1 := hIC2 y y'
    have h2 := hIC2 y' y
    rw [h] at h1
    rw [← h] at h2
    linarith
  let p : Finset (Fin n) → ℝ := fun T =>
    if h : ∃ y, m.alloc (Function.update v i y) = T then
      m.pay (Function.update v i (Classical.choose h)) i else 0
  have hp : ∀ y : ℝ≥0, m.pay (Function.update v i y) i = p (m.alloc (Function.update v i y)) := by
    intro y
    have hex : ∃ y', m.alloc (Function.update v i y') = m.alloc (Function.update v i y) :=
      ⟨y, rfl⟩
    simp only [p, dif_pos hex]
    exact hpay _ _ (Classical.choose_spec hex).symm
  refine ⟨p, hp, ?_⟩
  rintro y T ⟨y', rfl⟩
  rw [← hp, ← hp]
  exact hIC2 y y'
