-- Prove2me | solution 1 for SampleDrivenOS.Structure.lemma_17
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-23T22:49:48.209017+00:00
-- url     : https://prove2.me/submissions/98558c8b-50b1-4fc1-b364-279ad800d05e

import Mathlib
import Definitions.Def_SampleDrivenOS_Structure_Setting

open MeasureTheory Set

namespace SDOSL17
open SampleDrivenOS.Structure

lemma nb_succ (a m : ℕ) (t : ℝ) :
    nbTerm (a + m + 1) (a + 1) t =
      nbTerm (a + m) (a + 1) t + ((a + m).choose a : ℝ) * (1 - t) ^ m * t ^ (a + 1) := by
  unfold nbTerm
  rw [Finset.sum_Icc_succ_top (by omega)]
  congr 1
  have h1 : a + m + 1 - 1 = a + m := by omega
  have h2 : a + 1 - 1 = a := by omega
  have h3 : a + m + 1 - (a + 1) = m := by omega
  rw [h1, h2, h3]

lemma nb_zero (a : ℕ) (t : ℝ) : nbTerm a (a + 1) t = 0 := by
  unfold nbTerm
  have : Finset.Icc (a + 1) a = ∅ := by ext x; simp
  rw [this]; simp

/-- Derivative of the negative-binomial term (the paper's telescoped formula). -/
lemma nb_hasDeriv (a m : ℕ) (t : ℝ) :
    HasDerivAt (fun s => nbTerm (a + m) (a + 1) s)
      (((a + m).choose a : ℝ) * m * t ^ a * (1 - t) ^ (m - 1)) t := by
  induction m with
  | zero =>
    simp only [Nat.add_zero, CharP.cast_eq_zero, mul_zero, zero_mul]
    have : (fun s => nbTerm a (a + 1) s) = fun _ => (0 : ℝ) := by
      funext s; exact nb_zero a s
    rw [this]; exact hasDerivAt_const t 0
  | succ m ih =>
    have e : (fun s => nbTerm (a + (m + 1)) (a + 1) s) =
        fun s => nbTerm (a + m) (a + 1) s + ((a + m).choose a : ℝ) * (1 - s) ^ m * s ^ (a + 1) := by
      funext s
      have : a + (m + 1) = a + m + 1 := by omega
      rw [this, nb_succ]
    rw [e]
    have h2 : HasDerivAt (fun s : ℝ => ((a + m).choose a : ℝ) * (1 - s) ^ m * s ^ (a + 1))
        (((a + m).choose a : ℝ) * ((m : ℝ) * (1 - t) ^ (m - 1) * (-1)) * t ^ (a + 1) +
          ((a + m).choose a : ℝ) * (1 - t) ^ m * (((a + 1 : ℕ) : ℝ) * t ^ (a + 1 - 1))) t := by
      have hA : HasDerivAt (fun s : ℝ => (1 - s) ^ m) ((m : ℝ) * (1 - t) ^ (m - 1) * (-1)) t := by
        have h := (hasDerivAt_pow m (1 - t)).comp t ((hasDerivAt_id t).const_sub 1)
        refine h.congr_deriv ?_
        simp
      have hB : HasDerivAt (fun s : ℝ => s ^ (a + 1)) (((a + 1 : ℕ) : ℝ) * t ^ (a + 1 - 1)) t :=
        hasDerivAt_pow (a + 1) t
      exact (hA.const_mul _).mul hB
    refine (ih.add h2).congr_deriv ?_
    symm
    have hc : ((a + (m + 1)).choose a : ℝ) * ((m : ℝ) + 1) =
        ((a + m).choose a : ℝ) * ((a : ℝ) + m + 1) := by
      have := Nat.choose_mul_succ_eq (a + m) a
      have e1 : a + m + 1 - a = m + 1 := by omega
      rw [e1] at this
      have e2 : a + (m + 1) = a + m + 1 := by omega
      rw [e2]
      exact_mod_cast this.symm
    have e3 : a + 1 - 1 = a := by omega
    have e4 : m + 1 - 1 = m := by omega
    rw [e3, e4]
    push_cast
    rcases m with _ | m
    · push_cast at hc ⊢
      linear_combination (t ^ a) * hc
    · have e5 : m + 1 - 1 = m := by omega
      rw [e5]
      push_cast at hc ⊢
      linear_combination (t ^ a * (1 - t) ^ (m + 1)) * hc

end SDOSL17

open SampleDrivenOS.Structure in
theorem solution (k ℓ : ℕ) (hk : 1 ≤ k) (hℓ : 1 ≤ ℓ) (hℓk : ℓ ≤ k) :
    MonotoneOn (nbTerm k ℓ) (Icc 0 1) := by
  obtain ⟨a, rfl⟩ : ∃ a, ℓ = a + 1 := ⟨ℓ - 1, by omega⟩
  obtain ⟨m, rfl⟩ : ∃ m, k = a + m := ⟨k - a, by omega⟩
  have hd : ∀ t, HasDerivAt (nbTerm (a + m) (a + 1))
      (((a + m).choose a : ℝ) * m * t ^ a * (1 - t) ^ (m - 1)) t := fun t => SDOSL17.nb_hasDeriv a m t
  apply monotoneOn_of_deriv_nonneg (convex_Icc 0 1)
  · exact fun t _ => (hd t).continuousAt.continuousWithinAt
  · exact fun t _ => (hd t).differentiableAt.differentiableWithinAt
  · intro t ht
    rw [interior_Icc] at ht
    rw [(hd t).deriv]
    have h1 : 0 ≤ 1 - t := by linarith [ht.2]
    have h2 : 0 ≤ t := ht.1.le
    positivity
