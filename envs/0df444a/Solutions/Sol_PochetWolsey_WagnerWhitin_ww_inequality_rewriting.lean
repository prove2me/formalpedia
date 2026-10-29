-- Prove2me | solution 1 for PochetWolsey.WagnerWhitin.ww_inequality_rewriting
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-29T03:22:34.102114+00:00
-- url     : https://prove2.me/submissions/0340921a-89d9-4aa3-a3fe-c98919e183ba

import Mathlib

open scoped BigOperators

theorem solution (n : ℕ) (hn : 0 < n)
    (d x y : Fin n → ℝ) (s : Fin (n + 1) → ℝ)
    (hd : ∀ t, 0 ≤ d t) (hs0 : s 0 = 0)
    (hbalance : ∀ t, s t.castSucc + x t = d t + s t.succ)
    (k l : Fin n) (hkl : k ≤ l) :
    (s k.castSucc ≥ ∑ j ∈ Finset.Icc k l,
      d j * (1 - ∑ u ∈ Finset.Icc k j, y u) ↔
      s k.castSucc + ∑ j ∈ Finset.Icc k l,
        (∑ u ∈ Finset.Icc j l, d u) * y j ≥ ∑ j ∈ Finset.Icc k l, d j) ∧
    (s k.castSucc + ∑ j ∈ Finset.Icc k l,
        (∑ u ∈ Finset.Icc j l, d u) * y j ≥ ∑ j ∈ Finset.Icc k l, d j ↔
      (∑ j ∈ Finset.Iio k, x j) + ∑ j ∈ Finset.Icc k l,
        (∑ u ∈ Finset.Icc j l, d u) * y j ≥ ∑ j ∈ Finset.Iic l, d j) := by
  have key : ∑ j ∈ Finset.Icc k l, d j * (1 - ∑ u ∈ Finset.Icc k j, y u)
      = ∑ j ∈ Finset.Icc k l, d j - ∑ j ∈ Finset.Icc k l,
        (∑ u ∈ Finset.Icc j l, d u) * y j := by
    have h2 : ∑ j ∈ Finset.Icc k l, ∑ u ∈ Finset.Icc k j, d j * y u
        = ∑ u ∈ Finset.Icc k l, ∑ j ∈ Finset.Icc u l, d j * y u := by
      apply Finset.sum_comm'
      intro j u
      simp only [Finset.mem_Icc, Fin.le_def]
      constructor <;> intro h <;> omega
    simp only [mul_sub, mul_one, Finset.sum_sub_distrib, Finset.mul_sum, Finset.sum_mul] at h2 ⊢
    rw [h2]
  have tele : ∀ m (hm : m < n + 1), s ⟨m, hm⟩ =
      ∑ j ∈ Finset.univ.filter (fun j : Fin n => j.val < m), (x j - d j) := by
    intro m
    induction m with
    | zero =>
      intro hm
      have : (⟨0, hm⟩ : Fin (n+1)) = 0 := rfl
      rw [this, hs0]
      symm; apply Finset.sum_eq_zero; intro j hj; simp at hj
    | succ m ih =>
      intro hm
      have hm' : m < n := by omega
      have hb := hbalance ⟨m, hm'⟩
      have e1 : (⟨m, hm'⟩ : Fin n).castSucc = ⟨m, by omega⟩ := rfl
      have e2 : (⟨m, hm'⟩ : Fin n).succ = ⟨m+1, hm⟩ := rfl
      rw [e1, e2, ih (by omega)] at hb
      have hf : Finset.univ.filter (fun j : Fin n => j.val < m + 1)
          = insert ⟨m, hm'⟩ (Finset.univ.filter (fun j : Fin n => j.val < m)) := by
        ext j; simp [Fin.ext_iff]; omega
      rw [hf, Finset.sum_insert (by simp)]
      linarith
  have hsk : s k.castSucc = ∑ j ∈ Finset.Iio k, x j - ∑ j ∈ Finset.Iio k, d j := by
    have := tele k.val (by omega)
    have e : (⟨k.val, by omega⟩ : Fin (n+1)) = k.castSucc := rfl
    rw [e] at this
    rw [this, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr _ (fun _ _ => rfl)
    ext j; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_Iio, Fin.lt_def]
  have hsplit : ∑ j ∈ Finset.Iic l, d j = ∑ j ∈ Finset.Iio k, d j + ∑ j ∈ Finset.Icc k l, d j := by
    rw [← Finset.sum_union]
    · congr 1; ext j; simp only [Finset.mem_Iic, Finset.mem_union, Finset.mem_Iio, Finset.mem_Icc]
      simp only [Fin.le_def, Fin.lt_def]; rw [Fin.le_def] at hkl; omega
    · rw [Finset.disjoint_left]; intro j h1 h2
      simp only [Finset.mem_Iio, Finset.mem_Icc] at h1 h2
      exact absurd h2.1 (not_le.mpr h1)
  rw [key, hsplit, hsk]
  constructor <;> constructor <;> intro h <;> linarith
