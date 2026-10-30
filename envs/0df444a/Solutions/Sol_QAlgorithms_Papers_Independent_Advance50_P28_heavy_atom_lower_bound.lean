-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Advance50.P28.heavy_atom_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-29T10:50:09.390989+00:00
-- url     : https://prove2.me/submissions/1c1d9aa7-1353-4129-a5e1-1263be613e53

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P28
noncomputable section
open MeasureTheory Filter
open scoped BigOperators ENNReal Topology
open QAlgorithms.Papers.Independent.Advance50.P28
open QAlgorithms.Papers.Independent.Information100.P56 (IsLaw)
attribute [local instance] Classical.propDecidable Classical.decEq

theorem solution {A : Type*} [Fintype A] [Nonempty A]
    {M : ℕ} (hM : 0 < M) (P : A → ℝ) (hP : IsLaw P) (f : A → Fin M) :
    (∑ a, if 2 / (M : ℝ) ≤ P a then P a else 0) ≤ extractionError P f := by
  obtain ⟨hP0, hP1⟩ := hP
  have hMr : (0:ℝ) < M := by exact_mod_cast hM
  set h : Fin M → ℝ := fun b => ∑ a, if (2 / (M : ℝ) ≤ P a ∧ f a = b) then P a else 0 with hh
  set m : Fin M → ℝ := fun b => hashFiberMass P f b with hm
  have hsumh : ∑ b, h b = ∑ a, if 2 / (M : ℝ) ≤ P a then P a else 0 := by
    simp only [hh]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro a _
    by_cases ha : 2 / (M : ℝ) ≤ P a
    · simp [ha]
    · simp [ha]
  have hsumm : ∑ b, m b = 1 := by
    simp only [hm, hashFiberMass]
    rw [Finset.sum_comm]
    have : ∀ a : A, (∑ b : Fin M, if f a = b then P a else 0) = P a := by
      intro a; simp
    simp only [this]
    exact hP1
  have hx : ∑ b, (m b - 1 / (M:ℝ)) = 0 := by
    rw [Finset.sum_sub_distrib, hsumm]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rw [mul_one_div_cancel hMr.ne']
    ring
  have hpt : ∀ b, h b ≤ |m b - 1 / (M:ℝ)| + (m b - 1 / (M:ℝ)) := by
    intro b
    have hmh : h b ≤ m b := by
      simp only [hh, hm, hashFiberMass]
      apply Finset.sum_le_sum
      intro a _
      by_cases hc : (2 / (M : ℝ) ≤ P a ∧ f a = b)
      · rw [if_pos hc, if_pos hc.2]
      · rw [if_neg hc]
        split_ifs
        · exact hP0 a
        · exact le_rfl
    have hh0 : 0 ≤ h b := by
      apply Finset.sum_nonneg
      intro a _
      split_ifs
      · exact hP0 a
      · exact le_rfl
    by_cases h0 : h b = 0
    · rw [h0]
      linarith [neg_abs_le (m b - 1 / (M:ℝ))]
    · have hpos : 0 < h b := lt_of_le_of_ne hh0 (Ne.symm h0)
      obtain ⟨a, _, ha⟩ := Finset.exists_ne_zero_of_sum_ne_zero h0
      have hc : (2 / (M : ℝ) ≤ P a ∧ f a = b) := by
        by_contra hc; exact ha (if_neg hc)
      have hle : P a ≤ h b := by
        simp only [hh]
        have := Finset.single_le_sum (f := fun a' => if (2 / (M : ℝ) ≤ P a' ∧ f a' = b) then P a' else 0)
          (fun a' _ => by split_ifs; exact hP0 a'; exact le_rfl) (Finset.mem_univ a)
        simpa [hc] using this
      have h2 : 2 / (M:ℝ) ≤ h b := le_trans hc.1 hle
      have : 1 / (M:ℝ) ≤ h b / 2 := by
        have : 2 / (M:ℝ) = 2 * (1 / (M:ℝ)) := by ring
        linarith
      linarith [le_abs_self (m b - 1 / (M:ℝ))]
  unfold extractionError finiteVectorMass
  rw [hP1]
  rw [← hsumh]
  have := Finset.sum_le_sum (s := Finset.univ) (fun b _ => hpt b)
  rw [Finset.sum_add_distrib, hx, add_zero] at this
  exact this
