-- Prove2me | solution 1 for TalagrandConc.SKModel.lipschitz
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T07:26:31.402247+00:00
-- url     : https://prove2.me/submissions/4f4103c7-cdc3-4b1c-b50b-927b7f8c0d33

import Mathlib
import Definitions.Def_TalagrandConc_SKModel_Basic



namespace TalagrandConc.SKModel

lemma abs_spin {N : ℕ} (ε : Fin N → Bool) (i : Fin N) : |spin ε i| = 1 := by
  unfold spin; split_ifs <;> simp

lemma partitionFunction_pos (N : ℕ) (β : ℝ) (h : Interaction N → ℝ) :
    0 < partitionFunction N β h := by
  unfold partitionFunction
  apply mul_pos (by positivity)
  apply Finset.sum_pos (fun ε _ => Real.exp_pos _) Finset.univ_nonempty

lemma partitionFunction_le (N : ℕ) (β : ℝ) (h h' : Interaction N → ℝ)
    (hβ : 0 ≤ β) :
    partitionFunction N β h ≤
      Real.exp (β / Real.sqrt N * ∑ p : Interaction N, |h p - h' p|) *
        partitionFunction N β h' := by
  unfold partitionFunction
  rw [mul_left_comm]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro ε _
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  rw [← mul_add]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro p _
  have h1 := abs_spin ε p.1.1
  have h2 := abs_spin ε p.1.2
  have : h p * spin ε p.1.1 * spin ε p.1.2 - h' p * spin ε p.1.1 * spin ε p.1.2
      = (h p - h' p) * (spin ε p.1.1 * spin ε p.1.2) := by ring
  have h3 : |(h p - h' p) * (spin ε p.1.1 * spin ε p.1.2)| = |h p - h' p| := by
    rw [abs_mul, abs_mul, h1, h2]; ring
  have := le_abs_self ((h p - h' p) * (spin ε p.1.1 * spin ε p.1.2))
  linarith

lemma lipschitz_core (N : ℕ) (β : ℝ) (h h' : Interaction N → ℝ)
    (hN : 0 < N) (hβ : 0 < β) :
    |freeEnergy N β h - freeEnergy N β h'| ≤
      β / Real.sqrt N * ∑ p : Interaction N, |h p - h' p| := by
  unfold freeEnergy
  have key : ∀ a b : Interaction N → ℝ, Real.log (partitionFunction N β a) -
      Real.log (partitionFunction N β b) ≤
      β / Real.sqrt N * ∑ p : Interaction N, |a p - b p| := by
    intro a b
    have := partitionFunction_le N β a b hβ.le
    have hb := partitionFunction_pos N β b
    have ha := partitionFunction_pos N β a
    have := Real.log_le_log ha this
    rw [Real.log_mul (Real.exp_pos _).ne' hb.ne', Real.log_exp] at this
    linarith
  rw [abs_sub_le_iff]
  constructor
  · exact key h h'
  · have := key h' h
    simp_rw [abs_sub_comm (h' _) (h _)] at this
    exact this

end TalagrandConc.SKModel

open TalagrandConc.SKModel


theorem solution (N : ℕ) (β : ℝ) (h h' : Interaction N → ℝ)
    (hN : 0 < N) (hβ : 0 < β) :
    |freeEnergy N β h - freeEnergy N β h'| ≤
      β / Real.sqrt N * ∑ p : Interaction N, |h p - h' p| := by
  exact lipschitz_core N β h h' hN hβ
