-- Prove2me | solution 1 for StaticCalendar.lemma_EC_7
-- status  : ACCEPTED   (prove)
-- author  : @ducloc
-- created : 2026-11-12T13:16:21.807308+00:00
-- url     : https://prove2.me/submissions/76877d2f-4f12-4ee3-9b76-66a041d793ca

import Mathlib

set_option autoImplicit false

/-- Weighted Chebyshev, dual form: for positive `b`, an antitone ratio `a/b` and monotone
nonnegative weights `β`, the `β`-weighted average of the ratios is dominated by the unweighted one. -/
theorem solution {n : ℕ} (a b β : Fin (n + 1) → ℝ) (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 < b i)
    (hratio : Antitone fun i => a i / b i) (hβ : Monotone β) (hβ0 : ∀ i, 0 ≤ β i)
    (hβpos : ∃ i, 0 < β i) :
    (∑ i, β i * a i) / (∑ i, β i * b i) ≤ (∑ i, a i) / (∑ i, b i) := by
  classical
  have hanti : Antivary β (fun i => a i / b i) := by
    intro i j hij
    by_contra hle
    have hlt : β i < β j := lt_of_not_ge hle
    have hji : j ≤ i := by
      by_contra h
      have hij' : i ≤ j := le_of_lt (lt_of_not_ge h)
      exact absurd hij (not_lt.mpr (hratio hij'))
    exact absurd (hβ hji) (not_le.mpr hlt)
  have hterm : ∀ i j : Fin (n + 1), 0 ≤ (a i * b j - a j * b i) * (β j - β i) := by
    intro i j
    have hbij : 0 < b i * b j := mul_pos (hb i) (hb j)
    have hanti' : (β i - β j) * (a i / b i - a j / b j) ≤ 0 :=
      Antivary.sub_mul_sub_nonpos hanti j i
    have hbi : b i ≠ 0 := (hb i).ne'
    have hbj : b j ≠ 0 := (hb j).ne'
    have heq : (a i * b j - a j * b i) * (β j - β i)
        = -((b i * b j) * ((a i / b i - a j / b j) * (β i - β j))) := by
      field_simp [hbi, hbj]
      ring
    rw [heq]
    have hanti'' : (a i / b i - a j / b j) * (β i - β j) ≤ 0 := by
      simpa [mul_comm] using hanti'
    have hnn : (b i * b j) * ((a i / b i - a j / b j) * (β i - β j)) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hbij.le hanti''
    linarith
  have hS : 0 ≤ (∑ i, ∑ j, (a i * b j - a j * b i) * (β j - β i)) := by
    exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => hterm i j
  have h2 : 2 * (∑ i, ∑ j, a i * b j * (β j - β i))
      = ∑ i, ∑ j, (a i * b j - a j * b i) * (β j - β i) := by
    have hsplit : (∑ i, ∑ j, (a i * b j - a j * b i) * (β j - β i))
        = (∑ i, ∑ j, a i * b j * (β j - β i)) -
            (∑ i, ∑ j, a j * b i * (β j - β i)) := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro i _
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro j _
      ring
    have hswap : (∑ i, ∑ j, a j * b i * (β j - β i))
        = ∑ i, ∑ j, a i * b j * (β i - β j) := by
      rw [Finset.sum_comm]
    have hneg : (∑ i, ∑ j, a i * b j * (β i - β j))
        = -(∑ i, ∑ j, a i * b j * (β j - β i)) := by
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro i _
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro j _
      ring
    rw [hsplit, hswap, hneg]
    ring
  have hD : (∑ i, a i) * (∑ j, β j * b j) - (∑ i, β i * a i) * (∑ j, b j)
      = ∑ i, ∑ j, a i * b j * (β j - β i) := by
    rw [Finset.sum_mul_sum, Finset.sum_mul_sum]
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hmain : (∑ i, β i * a i) * (∑ j, b j) ≤ (∑ i, a i) * (∑ j, β j * b j) := by
    have hzero : 0 ≤ 2 * (∑ i, ∑ j, a i * b j * (β j - β i)) := by rw [h2]; exact hS
    linarith [hD]
  obtain ⟨i0, hi0⟩ := hβpos
  have hB : 0 < ∑ i, b i :=
    Finset.sum_pos (fun i _ => hb i) ⟨i0, Finset.mem_univ i0⟩
  have hBβ : 0 < ∑ i, β i * b i :=
    Finset.sum_pos' (fun i _ => mul_nonneg (hβ0 i) (hb i).le)
      ⟨i0, Finset.mem_univ i0, mul_pos hi0 (hb i0)⟩
  rw [div_le_div_iff₀ hBβ hB]
  exact hmain
