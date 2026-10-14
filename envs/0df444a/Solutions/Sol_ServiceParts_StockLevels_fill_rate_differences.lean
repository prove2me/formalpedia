-- Prove2me | solution 1 for ServiceParts.StockLevels.fill_rate_differences
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-13T03:27:57.704311+00:00
-- url     : https://prove2.me/submissions/248b6fbd-cb18-455c-b6b2-3c4957b002ca

import Mathlib
import Definitions.Def_ServiceParts_StockLevels_Basic



namespace ServiceParts.StockLevels

lemma fr_fdiff (a : ℝ) (s : ℕ) : fdiff (poissonFillRate a) s = poissonPmf a s := by
  simp [fdiff, poissonFillRate, Finset.sum_range_succ]

lemma fr_succ (a : ℝ) (s : ℕ) :
    poissonPmf a (s + 1) = poissonPmf a s * (a / ((s : ℝ) + 1)) := by
  unfold poissonPmf
  rw [Nat.factorial_succ]
  push_cast
  have : (s.factorial : ℝ) ≠ 0 := by positivity
  field_simp
  ring

lemma fr_pos (a : ℝ) (ha : 0 < a) (s : ℕ) : 0 < poissonPmf a s := by
  unfold poissonPmf; positivity

theorem fill_rate_differences_core (lam tbar : ℝ) (hlam : 0 < lam) (htbar : 0 < tbar) (s : ℕ) :
    fdiff (poissonFillRate (lam * tbar)) s = poissonPmf (lam * tbar) s ∧
    fdiff2 (poissonFillRate (lam * tbar)) s
      = poissonPmf (lam * tbar) (s + 1) - poissonPmf (lam * tbar) s ∧
    fdiff2 (poissonFillRate (lam * tbar)) s
      = poissonPmf (lam * tbar) s * (lam * tbar / ((s : ℝ) + 1) - 1) ∧
    ((s : ℝ) + 1 < lam * tbar → 0 < fdiff2 (poissonFillRate (lam * tbar)) s) ∧
    ((¬ ∃ n : ℕ, lam * tbar = n) →
      (fdiff2 (poissonFillRate (lam * tbar)) s ≤ 0 ↔ ⌊lam * tbar⌋₊ ≤ s)) ∧
    ((∃ n : ℕ, lam * tbar = n) →
      (fdiff2 (poissonFillRate (lam * tbar)) s ≤ 0 ↔ lam * tbar - 1 ≤ (s : ℝ))) := by
  set a := lam * tbar with ha_def
  have ha : 0 < a := mul_pos hlam htbar
  have h2 : fdiff2 (poissonFillRate a) s = poissonPmf a (s + 1) - poissonPmf a s := by
    simp only [fdiff2, fr_fdiff]
  have h3 : fdiff2 (poissonFillRate a) s = poissonPmf a s * (a / ((s : ℝ) + 1) - 1) := by
    rw [h2, fr_succ]; ring
  have hp := fr_pos a ha s
  have hs1 : (0 : ℝ) < (s : ℝ) + 1 := by positivity
  have hneg : fdiff2 (poissonFillRate a) s ≤ 0 ↔ a ≤ (s : ℝ) + 1 := by
    rw [h3]
    constructor
    · intro h
      have : a / ((s : ℝ) + 1) - 1 ≤ 0 := by
        by_contra hc; push_neg at hc; nlinarith [mul_pos hp hc]
      rw [sub_nonpos, div_le_one hs1] at this; exact this
    · intro h
      apply mul_nonpos_of_nonneg_of_nonpos hp.le
      rw [sub_nonpos, div_le_one hs1]; exact h
  refine ⟨fr_fdiff a s, h2, h3, ?_, ?_, ?_⟩
  · intro h
    rw [h3]
    apply mul_pos hp
    rw [sub_pos, one_lt_div hs1]; exact h
  · intro hn
    rw [hneg]
    have hfl : ⌊a⌋₊ ≤ s ↔ a < (s : ℝ) + 1 := by
      rw [← Nat.lt_succ_iff, Nat.floor_lt ha.le]; push_cast; rfl
    rw [hfl]
    constructor
    · intro h
      rcases h.lt_or_eq with h | h
      · exact h
      · exact absurd ⟨s + 1, by rw [h]; push_cast; rfl⟩ hn
    · exact le_of_lt
  · intro _
    rw [hneg]; constructor <;> intro h <;> linarith

end ServiceParts.StockLevels

open ServiceParts.StockLevels


theorem solution (lam tbar : ℝ) (hlam : 0 < lam) (htbar : 0 < tbar) (s : ℕ) :
    fdiff (poissonFillRate (lam * tbar)) s = poissonPmf (lam * tbar) s ∧
    fdiff2 (poissonFillRate (lam * tbar)) s
      = poissonPmf (lam * tbar) (s + 1) - poissonPmf (lam * tbar) s ∧
    fdiff2 (poissonFillRate (lam * tbar)) s
      = poissonPmf (lam * tbar) s * (lam * tbar / ((s : ℝ) + 1) - 1) ∧
    ((s : ℝ) + 1 < lam * tbar → 0 < fdiff2 (poissonFillRate (lam * tbar)) s) ∧
    ((¬ ∃ n : ℕ, lam * tbar = n) →
      (fdiff2 (poissonFillRate (lam * tbar)) s ≤ 0 ↔ ⌊lam * tbar⌋₊ ≤ s)) ∧
    ((∃ n : ℕ, lam * tbar = n) →
      (fdiff2 (poissonFillRate (lam * tbar)) s ≤ 0 ↔ lam * tbar - 1 ≤ (s : ℝ))) := by
  exact fill_rate_differences_core lam tbar hlam htbar s
