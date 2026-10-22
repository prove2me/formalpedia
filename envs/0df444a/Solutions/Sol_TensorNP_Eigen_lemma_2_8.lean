-- Prove2me | solution 1 for TensorNP.Eigen.lemma_2_8
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T13:06:41.721952+00:00
-- url     : https://prove2.me/submissions/9039e865-ad37-4216-843a-0d96b13459b9

import Mathlib
import Definitions.Def_TensorNP_Eigen_Construction

set_option autoImplicit false
open Matrix TensorNP.Eigen

theorem X_pad_lt {m n r s : ℕ} (A : Fin m → Matrix (Fin n) (Fin n) ℝ) (hs : n ≤ s)
    (k : Fin r) (hk : (k : ℕ) < m) (y : Fin s → ℝ) :
    y ⬝ᵥ (padSystem A r s k *ᵥ y) =
      (fun j : Fin n => y (Fin.castLE hs j)) ⬝ᵥ
        (A ⟨k, hk⟩ *ᵥ (fun j : Fin n => y (Fin.castLE hs j))) := by
  simp only [dotProduct, Matrix.mulVec]
  symm
  apply Fintype.sum_of_injective (Fin.castLE hs) (Fin.castLE_injective hs)
  · intro a ha
    have hna : ¬ (a : ℕ) < n := fun h => ha ⟨⟨a, h⟩, by ext; simp⟩
    simp [padSystem, hk, hna]
  · intro j
    congr 1
    apply Fintype.sum_of_injective (Fin.castLE hs) (Fin.castLE_injective hs)
    · intro b hb
      have hnb : ¬ (b : ℕ) < n := fun h => hb ⟨⟨b, h⟩, by ext; simp⟩
      simp [padSystem, hk, hnb]
    · intro j'
      simp [padSystem, hk]

theorem X_pad_last {m n r s : ℕ} (A : Fin m → Matrix (Fin n) (Fin n) ℝ)
    (k : Fin r) (hk : ¬ (k : ℕ) < m) (hkr : (k : ℕ) + 1 = r) (y : Fin s → ℝ) :
    y ⬝ᵥ (padSystem A r s k *ᵥ y) = ∑ a : Fin s, if n ≤ (a : ℕ) then y a ^ 2 else 0 := by
  simp only [dotProduct, Matrix.mulVec]
  refine Finset.sum_congr rfl fun a _ => ?_
  simp only [padSystem, hk, hkr, dif_neg, not_false_eq_true, if_true]
  by_cases ha : n ≤ (a : ℕ)
  · simp [ha, sq]
  · simp [ha]

theorem X_pad_other {m n r s : ℕ} (A : Fin m → Matrix (Fin n) (Fin n) ℝ)
    (k : Fin r) (hk : ¬ (k : ℕ) < m) (hkr : (k : ℕ) + 1 ≠ r) (y : Fin s → ℝ) :
    y ⬝ᵥ (padSystem A r s k *ᵥ y) = 0 := by
  simp [padSystem, hk, hkr, dotProduct, Matrix.mulVec]

theorem solution {m n r s : ℕ} (A : Fin m → Matrix (Fin n) (Fin n) ℝ) (hr : m + 1 ≤ r)
    (hs : n ≤ s) :
    QuadSolvable (padSystem A r s) ↔ QuadSolvable A := by
  constructor
  · rintro ⟨y, hy0, hy⟩
    have hlast := hy ⟨r - 1, by omega⟩
    rw [X_pad_last A ⟨r - 1, by omega⟩ (by simp; omega) (by simp; omega)] at hlast
    have hz : ∀ a : Fin s, n ≤ (a : ℕ) → y a = 0 := by
      intro a ha
      have hnn : ∀ a ∈ (Finset.univ : Finset (Fin s)), 0 ≤ (if n ≤ (a : ℕ) then y a ^ 2 else 0) := by
        intro a _
        split_ifs
        · positivity
        · exact le_refl _
      have := (Finset.sum_eq_zero_iff_of_nonneg hnn).1 hlast a (Finset.mem_univ _)
      rw [if_pos ha] at this
      exact pow_eq_zero_iff (two_ne_zero) |>.1 this
    refine ⟨fun j : Fin n => y (Fin.castLE hs j), ?_, fun i => ?_⟩
    · intro h0
      apply hy0
      funext a
      by_cases ha : (a : ℕ) < n
      · have := congrFun h0 ⟨a, ha⟩
        simpa using this
      · exact hz a (not_lt.1 ha)
    · have := hy ⟨i, by omega⟩
      rw [X_pad_lt A hs ⟨i, by omega⟩ (by simp)] at this
      simpa using this
  · rintro ⟨x, hx0, hx⟩
    let y : Fin s → ℝ := fun a => if h : (a : ℕ) < n then x ⟨a, h⟩ else 0
    have hye : ∀ j : Fin n, y (Fin.castLE hs j) = x j := by
      intro j; simp [y]
    refine ⟨y, ?_, fun k => ?_⟩
    · intro h0
      apply hx0
      funext j
      have := congrFun h0 (Fin.castLE hs j)
      rw [hye] at this
      simpa using this
    · by_cases hk : (k : ℕ) < m
      · rw [X_pad_lt A hs k hk]
        have : (fun j : Fin n => y (Fin.castLE hs j)) = x := funext hye
        rw [this]; exact hx ⟨k, hk⟩
      · by_cases hkr : (k : ℕ) + 1 = r
        · rw [X_pad_last A k hk hkr]
          apply Finset.sum_eq_zero
          intro a _
          by_cases ha : n ≤ (a : ℕ)
          · have : y a = 0 := by simp [y, not_lt.2 ha]
            simp [this]
          · simp [ha]
        · exact X_pad_other A k hk hkr y
