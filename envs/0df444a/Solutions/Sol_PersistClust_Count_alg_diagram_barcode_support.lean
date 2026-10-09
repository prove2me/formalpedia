-- Prove2me | solution 1 for PersistClust.Count.alg_diagram_barcode_support
-- status  : ACCEPTED   (prove)
-- author  : @fabianroll
-- created : 2026-10-09T11:32:38.830979+00:00
-- url     : https://prove2.me/submissions/d1dbc59b-a5d6-41f5-ab88-3c2eb1f7f5bf

import Mathlib
import Definitions.Def_PersistClust_Count_AlgBarcode

open PersistClust.Count
open scoped ENNReal

/-!
## Support (zero-mass) control for `ripsBarcode`

Purely structural: every point at which the combinatorial barcode is nonzero has a
real birth level equal to some `g r`, and a death coordinate that is either `-∞` (an
immortal bar) or a real level strictly below the birth level. No hypotheses on `Dm`
or `σ` are needed — it follows from the shape of the `barStep` sweep alone.
-/

namespace AlgBcSup

/-- The accumulator invariant. After any prefix of the `barRun` fold, the accumulated
off-diagonal multiplicity is nonzero only at points `((g r : EReal), (g i : EReal))`
with `g i < g r` — real coe birth/death, death strictly below birth. -/
def accSupport {n : ℕ} (g : Fin n → ℝ) (acc : EReal × EReal → ℕ∞) : Prop :=
  ∀ p, acc p ≠ 0 →
    ∃ r : Fin n, p.1 = (g r : EReal) ∧
      ∃ i : Fin n, p.2 = (g i : EReal) ∧ (g i : EReal) < (g r : EReal)

/-- In ℕ∞, `a + b ≠ 0` splits into `a ≠ 0 ∨ b ≠ 0`. -/
lemma add_ne_zero_split {a b : ℕ∞} (h : a + b ≠ 0) : a ≠ 0 ∨ b ≠ 0 := by
  rcases em (a = 0) with ha | ha
  · exact Or.inr fun hb => h (by rw [ha, hb]; rfl)
  · exact Or.inl ha

/-- The initial accumulator (constantly zero) satisfies the invariant. -/
lemma init_support {n : ℕ} (g : Fin n → ℝ) : accSupport g (fun _ => 0) := by
  intro p hp
  exact (hp rfl).elim

/-- A sum of death-point indicators that is nonzero contains a death point of the form
`((g r : EReal), (g i : EReal))`, for some `r` in the summed finset. -/
lemma sum_indicator_death {n : ℕ} (g : Fin n → ℝ) (s : Finset (Fin n)) (i : Fin n)
    (p : EReal × EReal)
    (hsum : s.sum (fun r => if p = ((g r : EReal), (g i : EReal)) then (1 : ℕ∞) else 0) ≠ 0) :
    ∃ r ∈ s, p = ((g r : EReal), (g i : EReal)) := by
  have hf : ∀ a ∈ s, 0 ≤ (if p = ((g a : EReal), (g i : EReal)) then (1 : ℕ∞) else 0) := by
    intro a _
    split_ifs <;> simp
  have h3 : ¬ ∀ a ∈ s, (if p = ((g a : EReal), (g i : EReal)) then (1 : ℕ∞) else 0) = 0 :=
    fun hall => hsum ((Finset.sum_eq_zero_iff_of_nonneg hf).mpr hall)
  push Not at h3
  obtain ⟨r, hr_mem, hr_ne⟩ := h3
  refine ⟨r, hr_mem, ?_⟩
  by_contra hne
  rw [if_neg hne] at hr_ne
  exact hr_ne rfl

/-- A sum of immortal-point indicators that is nonzero contains an immortal point of
the form `((g r : EReal), ⊥)`. -/
lemma sum_indicator_immortal {n : ℕ} (g : Fin n → ℝ) (s : Finset (Fin n)) (p : EReal × EReal)
    (hsum : s.sum (fun r => if p = ((g r : EReal), ⊥) then (1 : ℕ∞) else 0) ≠ 0) :
    ∃ r : Fin n, p = ((g r : EReal), ⊥) := by
  have hf : ∀ a ∈ s, 0 ≤ (if p = ((g a : EReal), ⊥) then (1 : ℕ∞) else 0) := by
    intro a _
    split_ifs <;> simp
  have h3 : ¬ ∀ a ∈ s, (if p = ((g a : EReal), ⊥) then (1 : ℕ∞) else 0) = 0 :=
    fun hall => hsum ((Finset.sum_eq_zero_iff_of_nonneg hf).mpr hall)
  push Not at h3
  obtain ⟨r, _, hr_ne⟩ := h3
  refine ⟨r, ?_⟩
  by_contra hne
  rw [if_neg hne] at hr_ne
  exact hr_ne rfl

/-- One `barStep` preserves the accumulator invariant: it either leaves the accumulator
untouched (no neighbour is already alive) or adds indicator masses at the death points
`((g r : EReal), (g i : EReal))` with `g i < g r` (the `dying` filter). -/
lemma barStep_support {n : ℕ} (g : Fin n → ℝ) (Dm : Fin n → Fin n → ℝ) (δ : ℝ)
    (σ : Fin n ≃ Fin n) (st : UFState n × ((EReal × EReal) → ℕ∞)) (i : Fin n)
    (h : accSupport g st.2) :
    accSupport g (barStep g Dm δ σ st i).2 := by
  simp only [barStep]
  split_ifs with hS
  · -- no neighbour alive yet: accumulator unchanged.
    exact h
  · -- merge step: accumulator gains `dying.sum (indicator …)`.
    intro p hp
    rcases add_ne_zero_split hp with hacc | hsum
    · exact h p hacc
    · -- a death pair `((g r), (g i))` was recorded by some dying root `r`.
      obtain ⟨r, hr_mem, hr_p⟩ := sum_indicator_death g _ i p hsum
      obtain ⟨hr1, hr2⟩ := Prod.ext_iff.mp hr_p
      have hlt : (g i : EReal) < (g r : EReal) := (Finset.mem_filter.mp hr_mem).2
      exact ⟨r, hr1, i, hr2, hlt⟩

/-- Folding `barStep` over any list preserves the invariant. -/
lemma foldl_support {n : ℕ} (g : Fin n → ℝ) (Dm : Fin n → Fin n → ℝ) (δ : ℝ)
    (σ : Fin n ≃ Fin n) (l : List (Fin n))
    (init : UFState n × ((EReal × EReal) → ℕ∞)) (h : accSupport g init.2) :
    accSupport g (l.foldl (fun st k => barStep g Dm δ σ st (σ k)) init).2 := by
  induction l generalizing init with
  | nil => simp only [List.foldl_nil]; exact h
  | cons k ks ih =>
    simp only [List.foldl_cons]
    exact ih _ (barStep_support g Dm δ σ _ (σ k) h)

/-- The full `barRun` accumulator satisfies the invariant. -/
lemma barRun_support {n : ℕ} (g : Fin n → ℝ) (Dm : Fin n → Fin n → ℝ) (δ : ℝ)
    (σ : Fin n ≃ Fin n) : accSupport g (barRun g Dm δ σ).2 := by
  simp only [barRun]
  exact foldl_support g Dm δ σ _ _ (init_support g)

end AlgBcSup

theorem solution
    (n : ℕ) (g : Fin n → ℝ) (Dm : Fin n → Fin n → ℝ) (δ : ℝ) (σ : Fin n ≃ Fin n)
    (p : EReal × EReal) (hp : ripsBarcode g Dm δ σ p ≠ 0) :
    ∃ r : Fin n, p.1 = ((g r : EReal)) ∧
      (p.2 = ⊥ ∨ ∃ d : ℝ, p.2 = ((d : EReal)) ∧ ((d : EReal)) < ((g r : EReal))) := by
  have hrun := AlgBcSup.barRun_support g Dm δ σ
  simp only [ripsBarcode] at hp
  -- `hp : (barRun …).2 p + immortals.sum (indicator at `((g r), ⊥)`) ≠ 0`
  rcases AlgBcSup.add_ne_zero_split hp with hacc | himm
  · -- off-diagonal (finite-death) contribution.
    obtain ⟨r, hr1, i, hi2, hilt⟩ := hrun p hacc
    exact ⟨r, hr1, Or.inr ⟨g i, hi2, hilt⟩⟩
  · -- immortal contribution: a point `((g r), ⊥)`.
    obtain ⟨r, hr_p⟩ := AlgBcSup.sum_indicator_immortal g _ p himm
    obtain ⟨hr1, hr2⟩ := Prod.ext_iff.mp hr_p
    exact ⟨r, hr1, Or.inl hr2⟩
