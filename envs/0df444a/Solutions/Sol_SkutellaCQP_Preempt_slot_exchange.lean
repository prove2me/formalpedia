-- Prove2me | solution 1 for SkutellaCQP.Preempt.slot_exchange
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-07T08:24:31.313874+00:00
-- url     : https://prove2.me/submissions/577778fd-7ff2-450d-b066-9fcd475a1999

import Mathlib
import Definitions.Def_SkutellaCQP_Preempt_Setting

open Finset SkutellaCQP.Preempt

theorem solution {m n : ℕ} (p : Fin m → Fin n → ℝ) (w : Fin n → ℝ)
    (hp : ∀ i j, 0 < p i j) (hw : ∀ j, 0 ≤ w j)
    (i : Fin m) (x : Fin n → ℝ) (hx : ∀ j, 0 ≤ x j) (π : Equiv.Perm (Fin n)) :
    ∑ j, x j * w j * ∑ j' ∈ univ.filter (fun j' => SkutellaCQP.NoRel.prec p w i j' j), x j' * p i j' ≤
      ∑ j, x j * w j * ∑ j' ∈ univ.filter (fun j' => π j' < π j), x j' * p i j' := by
  classical
  let A (j k : Fin n) : ℝ := if SkutellaCQP.NoRel.prec p w i k j then x j * w j * (x k * p i k) else 0
  let B (j k : Fin n) : ℝ := if π k < π j then x j * w j * (x k * p i k) else 0
  have pair (j k : Fin n) : A j k + A k j ≤ B j k + B k j := by
    by_cases he : j = k
    · subst k
      simp [A, B, SkutellaCQP.NoRel.prec]
    have hπ : π j ≠ π k := fun h => he (π.injective h)
    have htot : SkutellaCQP.NoRel.prec p w i j k ∨ SkutellaCQP.NoRel.prec p w i k j := by
      unfold SkutellaCQP.NoRel.prec
      rcases lt_trichotomy (w j * p i k) (w k * p i j) with h | h | h
      · exact Or.inr (Or.inl h)
      · rcases lt_or_gt_of_ne he with hh | hh
        · exact Or.inl (Or.inr ⟨h, hh⟩)
        · exact Or.inr (Or.inr ⟨h.symm, hh⟩)
      · exact Or.inl (Or.inl h)
    have hn : ¬ (SkutellaCQP.NoRel.prec p w i j k ∧ SkutellaCQP.NoRel.prec p w i k j) := by
      simp only [SkutellaCQP.NoRel.prec]
      intro h
      rcases h with ⟨h₁, h₂⟩
      rcases h₁ with h₁ | ⟨h₁, hjk⟩ <;> rcases h₂ with h₂ | ⟨h₂, hkj⟩ <;> first | linarith | exact (not_lt_of_ge hjk.le hkj)
    have hπtot : π j < π k ∨ π k < π j := lt_or_gt_of_ne hπ
    have scaled₁ (h : w j * p i k ≤ w k * p i j) :
        x k * w k * (x j * p i j) ≥ x j * w j * (x k * p i k) := by
      have hh := mul_le_mul_of_nonneg_left h (mul_nonneg (hx j) (hx k))
      nlinarith only [hh]
    have scaled₂ (h : w k * p i j ≤ w j * p i k) :
        x j * w j * (x k * p i k) ≥ x k * w k * (x j * p i j) := by
      have hh := mul_le_mul_of_nonneg_left h (mul_nonneg (hx j) (hx k))
      nlinarith only [hh]
    rcases htot with horder | horder
    · have hrev : ¬ SkutellaCQP.NoRel.prec p w i k j := fun h => hn ⟨horder, h⟩
      have hcoeff : w k * p i j ≤ w j * p i k := by
        rcases horder with h | ⟨h, _⟩ <;> linarith
      rcases hπtot with hπorder | hπorder
      · simp [A, B, horder, hrev, hπorder, not_lt_of_ge hπorder.le]
      · simpa [A, B, horder, hrev, hπorder, not_lt_of_ge hπorder.le] using scaled₂ hcoeff
    · have hrev : ¬ SkutellaCQP.NoRel.prec p w i j k := fun h => hn ⟨h, horder⟩
      have hcoeff : w j * p i k ≤ w k * p i j := by
        rcases horder with h | ⟨h, _⟩ <;> linarith
      rcases hπtot with hπorder | hπorder
      · simpa [A, B, horder, hrev, hπorder, not_lt_of_ge hπorder.le] using scaled₁ hcoeff
      · simp [A, B, horder, hrev, hπorder, not_lt_of_ge hπorder.le]
  have hh := sum_le_sum (fun j (_ : j ∈ (univ : Finset (Fin n))) =>
    sum_le_sum (fun k (_ : k ∈ (univ : Finset (Fin n))) => pair j k))
  simp only [sum_add_distrib] at hh
  have hswapA : (∑ j, ∑ k, A k j) = ∑ j, ∑ k, A j k := sum_comm
  have hswapB : (∑ j, ∑ k, B k j) = ∑ j, ∑ k, B j k := sum_comm
  rw [hswapA, hswapB] at hh
  have ha : (∑ j, ∑ k, A j k) = ∑ j, x j * w j *
      ∑ k ∈ univ.filter (fun k => SkutellaCQP.NoRel.prec p w i k j), x k * p i k := by
    simp [A, sum_filter, mul_sum, mul_ite]
  have hb : (∑ j, ∑ k, B j k) = ∑ j, x j * w j *
      ∑ k ∈ univ.filter (fun k => π k < π j), x k * p i k := by
    simp [B, sum_filter, mul_sum, mul_ite]
  rw [ha, hb] at hh
  linarith

#print axioms solution
