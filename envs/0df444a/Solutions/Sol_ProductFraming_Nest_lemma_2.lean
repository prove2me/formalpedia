-- Prove2me | solution 1 for ProductFraming.Nest.lemma_2
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-05T06:52:14.510874+00:00
-- url     : https://prove2.me/submissions/08359d4b-f2bf-4cc5-a4db-c096e7a2ca99

import Mathlib
import Definitions.Def_ProductFraming_Nest_Model
import Theorems.Thm_ProductFraming_Nest_lemma_1

open Finset ProductFraming.Nest

namespace PFNLemma2Aux

lemma U_nonneg {n : ℕ} (p : ℕ) (r : Fin n → ℝ) (P : Fin n → Finset (Fin n) → ℝ) (x : ℕ) :
    0 ≤ U p r P x := by
  unfold U G
  have hmem : (∅ : Finset (Fin n)) ∈ univ.filter (fun S : Finset (Fin n) => S.card ≤ x * p) := by
    simp
  have := Finset.le_sup' (R r P) hmem
  simpa [R] using this

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

end PFNLemma2Aux

open PFNLemma2Aux in
theorem solution (n m p : ℕ) (hm : 1 ≤ m) (hp : 1 ≤ p) (r : Fin n → ℝ) (hr : ∀ i, 0 ≤ r i)
    (P : Fin n → Finset (Fin n) → ℝ) (hP : IsChoiceModel P) (hA1 : SatisfiesA1 P) :
    ∀ x ∈ Icc 1 m, ∀ x' ∈ Icc 1 m, x ≤ x' →
      U p r P x' / (x' : ℝ) ≤ U p r P x / (x : ℝ) := by
  intro x hx x' hx' hxx'
  rw [mem_Icc] at hx hx'
  have hxpos : (0 : ℝ) < x := by exact_mod_cast hx.1
  have hx'pos : (0 : ℝ) < x' := by exact_mod_cast (le_trans hx.1 hxx')
  have hxx'R : (x : ℝ) ≤ x' := by exact_mod_cast hxx'
  -- an optimal assortment for `U(x')`
  obtain ⟨S, hS, hSeq⟩ := Finset.exists_mem_eq_sup'
    ⟨∅, by simp⟩ (R r P) (s := univ.filter (fun S : Finset (Fin n) => S.card ≤ x' * p))
  have hUx' : U p r P x' = R r P S := hSeq
  simp only [mem_filter, mem_univ, true_and] at hS
  have hRS : 0 ≤ R r P S := hUx' ▸ U_nonneg p r P x'
  have hUle : ∀ T : Finset (Fin n), T.card ≤ x * p → R r P T ≤ U p r P x := by
    intro T hT
    unfold U G
    apply Finset.le_sup' (R r P)
    simpa using hT
  by_cases hsmall : S.card ≤ x * p
  · have h1 := hUle S hsmall
    rw [hUx']
    calc R r P S / (x' : ℝ) ≤ R r P S / x := div_le_div_of_nonneg_left hRS hxpos hxx'R
      _ ≤ U p r P x / x := div_le_div_of_nonneg_right h1 hxpos.le
  · push_neg at hsmall
    have hk : 1 ≤ x * p := by simpa using Nat.mul_le_mul hx.1 hp
    obtain ⟨T, _, hTc, hTle⟩ := iter n r hr P hP hA1 (x * p) hk (S.card - x * p) S (by omega)
    have h1 := hUle T hTc.le
    have hSc : (0 : ℝ) < S.card := by exact_mod_cast (by omega : 0 < S.card)
    have hSc' : (S.card : ℝ) ≤ x' * p := by exact_mod_cast hS
    have hpR : (0 : ℝ) < p := by exact_mod_cast hp
    rw [hTc] at hTle
    push_cast at hTle
    rw [hUx', div_le_div_iff₀ hx'pos hxpos]
    -- `R(T) ≥ x p R(S)/|S| ≥ x R(S)/x'`
    have h2 : R r P S * (x * p) ≤ R r P T * S.card := by
      rw [div_le_div_iff₀ hSc (by positivity)] at hTle; linarith
    have h3 : R r P S * x * (S.card : ℝ) ≤ R r P S * x * (x' * p) :=
      mul_le_mul_of_nonneg_left hSc' (by positivity)
    have h4 : R r P T * x' ≤ U p r P x * x' := mul_le_mul_of_nonneg_right h1 hx'pos.le
    have h2' := mul_le_mul_of_nonneg_left h2 hx'pos.le
    have h5 : R r P S * x ≤ R r P T * x' := by
      have : R r P S * x * S.card ≤ R r P T * x' * S.card := by nlinarith [h3, h2']
      exact le_of_mul_le_mul_right this hSc
    linarith
