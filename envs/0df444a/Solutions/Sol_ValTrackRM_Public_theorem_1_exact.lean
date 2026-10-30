-- Prove2me | solution 1 for ValTrackRM.Public.theorem_1_exact
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-30T05:26:57.176853+00:00
-- url     : https://prove2.me/submissions/3c677aaf-fd17-4c72-97ff-8d5484ba955f

import Mathlib
import Definitions.Def_ValTrackRM_Public_Model
import Theorems.Thm_ValTrackRM_Public_lemma_EC_3
import Theorems.Thm_ValTrackRM_Public_lemma_EC_4
import Theorems.Thm_ValTrackRM_Public_opt_eq_sum_topK

open ValTrackRM.Public

namespace VTSolR

variable {m k : ℕ}

lemma r_strict (r : ℕ → ℝ) (hr : ∀ j, j < m → r j < r (j + 1)) :
    ∀ a b, a < b → b ≤ m → r a < r b := by
  intro a b
  induction b with
  | zero => intro h; omega
  | succ b ih =>
    intro h hb
    rcases Nat.lt_succ_iff_lt_or_eq.mp h with h1 | h1
    · exact (ih h1 (by omega)).trans (hr b (by omega))
    · subst h1; exact hr a (by omega)

lemma r_mono (r : ℕ → ℝ) (hr : ∀ j, j < m → r j < r (j + 1)) :
    ∀ a b, a ≤ b → b ≤ m → r a ≤ r b := by
  intro a b h hb
  rcases h.lt_or_eq with h | h
  · exact (r_strict r hr a b h hb).le
  · rw [h]

lemma r_le_iff (r : ℕ → ℝ) (hr : ∀ j, j < m → r j < r (j + 1)) (a b : ℕ) (ha : a ≤ m)
    (hb : b ≤ m) : r a ≤ r b ↔ a ≤ b := by
  constructor
  · intro h; by_contra h'; push Not at h'
    exact absurd h (not_le.mpr (r_strict r hr b a h' ha))
  · intro h; exact r_mono r hr a b h hb

lemma r_pos (r : ℕ → ℝ) (hr0 : r 0 = 0) (hr : ∀ j, j < m → r j < r (j + 1)) (j : ℕ)
    (h1 : 1 ≤ j) (h2 : j ≤ m) : 0 < r j := by
  have := r_strict r hr 0 j (by omega) h2
  rwa [hr0] at this

lemma r_nonneg (r : ℕ → ℝ) (hr0 : r 0 = 0) (hr : ∀ j, j < m → r j < r (j + 1)) (j : ℕ)
    (h2 : j ≤ m) : 0 ≤ r j := by
  have := r_mono r hr 0 j (by omega) h2
  rwa [hr0] at this

lemma qj_pos (r : ℕ → ℝ) (hr0 : r 0 = 0) (hr : ∀ j, j < m → r j < r (j + 1)) (p : ℕ)
    (h1 : 1 ≤ p) (h2 : p ≤ m) : 0 < qj r p := by
  unfold qj
  have hp := r_pos r hr0 hr p h1 h2
  have hlt := r_strict r hr (p - 1) p (by omega) h2
  have : r (p - 1) / r p < 1 := (div_lt_one hp).mpr hlt
  linarith

lemma qj_mul (r : ℕ → ℝ) (hr0 : r 0 = 0) (hr : ∀ j, j < m → r j < r (j + 1)) (p : ℕ)
    (h1 : 1 ≤ p) (h2 : p ≤ m) : qj r p * r p = r p - r (p - 1) := by
  unfold qj
  have hp := r_pos r hr0 hr p h1 h2
  field_simp

lemma sum_Icc_eq_Ioc (f : ℕ → ℝ) (n : ℕ) : ∑ j ∈ Finset.Icc 1 n, f j = ∑ j ∈ Finset.Ioc 0 n, f j := by
  rfl

lemma qSum_split (r : ℕ → ℝ) (ℓ : ℕ) (hℓ : ℓ ≤ m) :
    qSum r m = ∑ j ∈ Finset.Icc 1 ℓ, qj r j + qTot r m ℓ := by
  unfold qSum qTot
  rw [sum_Icc_eq_Ioc, sum_Icc_eq_Ioc, Finset.sum_Ioc_consecutive _ (Nat.zero_le ℓ) hℓ]

lemma qTot_pos (r : ℕ → ℝ) (hr0 : r 0 = 0) (hr : ∀ j, j < m → r j < r (j + 1)) (ℓ : ℕ)
    (hℓ : ℓ < m) : 0 < qTot r m ℓ := by
  unfold qTot
  apply Finset.sum_pos
  · intro p hp; simp at hp; exact qj_pos r hr0 hr p (by omega) (by omega)
  · exact ⟨m, by simp; omega⟩

lemma qSum_pos (r : ℕ → ℝ) (hr0 : r 0 = 0) (hr : ∀ j, j < m → r j < r (j + 1)) (hm : 1 ≤ m) :
    0 < qSum r m := by
  have := qSum_split (m := m) r 0 (by omega)
  have h2 := qTot_pos r hr0 hr 0 (by omega)
  simp at this; linarith


end VTSolR

theorem solution {m k : ℕ} (hm : 1 ≤ m) (hk : 1 ≤ k) (r : ℕ → ℝ) (hr0 : r 0 = 0)
    (hr : ∀ j, j < m → r j < r (j + 1))
    (sel : (Fin k → Fin (m + 1)) → Fin k) (hsel : ∀ (L : Fin k → Fin (m + 1)) (i : Fin k), L (sel L) ≤ L i)
    (V : List (Fin (m + 1))) :
    opt r k V = ∑ i, r (levels sel V i) ∧
      ∑ i, r (levels sel V i) = qSum r m * expRevenue r sel V := by
  have h4 := lemma_EC_4 hm hk r hr0 hr sel hsel V V.length le_rfl
  have h3 := lemma_EC_3 hm hk r hr0 hr sel hsel V V.length le_rfl
  have ho := opt_eq_sum_topK hm hk r hr0 hr sel hsel V
  rw [List.take_length] at h4 h3
  have hq := VTSolR.qSum_pos r hr0 hr hm
  constructor
  · rw [ho, ← h4.sum_eq, List.sum_ofFn]
  · unfold expRevenue
    rw [h3]
    field_simp
