-- Prove2me | solution 1 for ProductFraming.Nest.nest_run_exists
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-05T06:57:10.059474+00:00
-- url     : https://prove2.me/submissions/49f4e325-00b5-40c7-a796-5ea23fa71abc

import Mathlib
import Definitions.Def_ProductFraming_Nest_Model
import Definitions.Def_ProductFraming_Nest_Algorithm
import Theorems.Thm_ProductFraming_Nest_lemma_1

open Finset ProductFraming.Nest

namespace PFNRunAux

/-- Iterating Lemma 1: from any `S` one can remove products one at a time down to any size
`k ≥ 1` without lowering the revenue per product. -/
lemma iter (n : ℕ) (r : Fin n → ℝ) (hr : ∀ i, 0 ≤ r i) (P : Fin n → Finset (Fin n) → ℝ)
    (hP : IsChoiceModel P) (hA1 : SatisfiesA1 P) (k : ℕ) (hk : 1 ≤ k) :
    ∀ d, ∀ S : Finset (Fin n), S.card = k + d →
      ∃ T ⊆ S, T.card = k ∧ R r P S / (S.card : ℝ) ≤ R r P T / (T.card : ℝ) := by
  intro d
  induction d with
  | zero => intro S hS; exact ⟨S, subset_refl S, by simpa using hS, le_refl _⟩
  | succ d ih =>
    intro S hS
    obtain ⟨i, hi, hle⟩ := lemma_1 n r hr P hP hA1 S (by omega)
    have hcard : (S.erase i).card = k + d := by rw [card_erase_of_mem hi]; omega
    obtain ⟨T, hT, hTc, hTle⟩ := ih (S.erase i) hcard
    refine ⟨T, hT.trans (erase_subset i S), hTc, le_trans hle ?_⟩
    have : ((S.erase i).card : ℝ) = (S.card : ℝ) - 1 := by
      rw [card_erase_of_mem hi]
      have : 1 ≤ S.card := by omega
      push_cast [this]; ring
    rw [← this]; exact hTle

/-- One step of NEST(y): a subset of `T` of size `min(|T|, c)` with no smaller revenue per
product, for `c ≥ 1`. -/
lemma step_exists (n : ℕ) (r : Fin n → ℝ) (hr : ∀ i, 0 ≤ r i) (P : Fin n → Finset (Fin n) → ℝ)
    (hP : IsChoiceModel P) (hA1 : SatisfiesA1 P) (T : Finset (Fin n)) (c : ℕ) (hc : 1 ≤ c) :
    ∃ T' ⊆ T, T'.card = min T.card c ∧ R r P T / (T.card : ℝ) ≤ R r P T' / (T'.card : ℝ) := by
  by_cases h : T.card ≤ c
  · exact ⟨T, subset_refl T, (min_eq_left h).symm, le_refl _⟩
  · push_neg at h
    obtain ⟨T', h1, h2, h3⟩ := iter n r hr P hP hA1 c hc (T.card - c) T (by omega)
    exact ⟨T', h1, by rw [h2]; omega, h3⟩

end PFNRunAux

open PFNRunAux in
theorem solution (n m p : ℕ) (hm : 1 ≤ m) (hp : 1 ≤ p) (r : Fin n → ℝ) (hr : ∀ i, 0 ≤ r i)
    (P : Fin n → Finset (Fin n) → ℝ) (hP : IsChoiceModel P) (hA1 : SatisfiesA1 P) :
    ∀ y ∈ Icc 1 m, ∃ S : ℕ → Finset (Fin n), IsNestRun p r P y S := by
  classical
  intro y hy
  rw [mem_Icc] at hy
  -- step 1: an optimal assortment for (2) with `c = y p`
  obtain ⟨S0, hS0, hS0eq⟩ := Finset.exists_mem_eq_sup'
    ⟨∅, by simp⟩ (R r P) (s := univ.filter (fun S : Finset (Fin n) => S.card ≤ y * p))
  simp only [mem_filter, mem_univ, true_and] at hS0
  -- step 2: the downward recursion
  let step : Finset (Fin n) → ℕ → Finset (Fin n) := fun T c =>
    if hc : 1 ≤ c then Classical.choose (step_exists n r hr P hP hA1 T c hc) else T
  have hstep : ∀ T c, 1 ≤ c → step T c ⊆ T ∧ (step T c).card = min T.card c ∧
      R r P T / (T.card : ℝ) ≤ R r P (step T c) / ((step T c).card : ℝ) := by
    intro T c hc
    simp only [step, dif_pos hc]
    exact Classical.choose_spec (step_exists n r hr P hP hA1 T c hc)
  let seqf : ℕ → Finset (Fin n) := fun k => Nat.rec S0 (fun k T => step T ((y - (k + 1)) * p)) k
  have hseq : ∀ k, seqf (k + 1) = step (seqf k) ((y - (k + 1)) * p) := fun k => rfl
  refine ⟨fun x => seqf (y - x), ?_, ?_⟩
  · simp only [Nat.sub_self]
    exact ⟨hS0, hS0eq.symm⟩
  · intro x hx hxy
    have hk : y - x = (y - (x + 1)) + 1 := by omega
    have hc : y - ((y - (x + 1)) + 1) = x := by omega
    simp only
    rw [hk, hseq, hc]
    have hxp : 1 ≤ x * p := by simpa using Nat.mul_le_mul hx hp
    obtain ⟨h1, h2, h3⟩ := hstep (seqf (y - (x + 1))) (x * p) hxp
    exact ⟨h1, h2, h3⟩
