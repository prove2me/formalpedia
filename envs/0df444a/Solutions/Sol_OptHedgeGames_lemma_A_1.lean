-- Prove2me | solution 1 for OptHedgeGames.lemma_A_1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-08T14:32:06.186586+00:00
-- url     : https://prove2.me/submissions/55fe93e3-4d79-4f4a-b020-d181977a975f

import Mathlib
import Definitions.Def_OptHedgeGames_Notation

namespace Aux_OptHedgeA1
open OptHedgeGames

lemma var_le_center {n : ℕ} (p v : Fin n → ℝ) (hp1 : ∑ a, p a = 1) (m : ℝ) :
    var p v ≤ ∑ a, p a * (v a - m) ^ 2 := by
  unfold var
  set μ := ∑ c, p c * v c with hμ
  have e : ∀ a, p a * (v a - m) ^ 2 = p a * (v a - μ) ^ 2 + (2 * (μ - m)) * (p a * v a)
      - (2 * (μ - m) * μ - (μ - m) ^ 2) * p a := by
    intro a; ring
  rw [Finset.sum_congr rfl (fun a _ => e a), Finset.sum_sub_distrib, Finset.sum_add_distrib,
    ← Finset.mul_sum, ← Finset.mul_sum, ← hμ, hp1]
  nlinarith [sq_nonneg (μ - m)]

end Aux_OptHedgeA1

open OptHedgeGames Aux_OptHedgeA1 in
theorem solution {n : ℕ} (p p' : Fin n → ℝ) (hp : p ∈ stdSimplex ℝ (Fin n))
    (hp' : p' ∈ stdSimplex ℝ (Fin n)) (u v : Fin n → ℝ) :
    (∀ Γ : ℝ, (∀ a, p' a ≤ Γ * p a) → var p' v ≤ Γ * var p v) ∧
      var p (u + v) ≤ 2 * var p u + 2 * var p v ∧
      (∀ lo b : ℝ, (∀ a, v a ∈ Set.Icc lo (lo + b)) → var p v ≤ b ^ 2 / 4) ∧
      var p v ≤ ‖v‖ ^ 2 := by
  obtain ⟨hp0, hp1⟩ := hp
  obtain ⟨hp0', hp1'⟩ := hp'
  refine ⟨fun Γ hΓ => ?_, ?_, fun lo b hb => ?_, ?_⟩
  · refine (var_le_center p' v hp1' (∑ c, p c * v c)).trans ?_
    unfold var
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum (fun a _ => ?_)
    rw [← mul_assoc]
    exact mul_le_mul_of_nonneg_right (hΓ a) (sq_nonneg _)
  · refine (var_le_center p (u + v) hp1 (∑ c, p c * u c + ∑ c, p c * v c)).trans ?_
    have h : ∀ a, p a * ((u + v) a - (∑ c, p c * u c + ∑ c, p c * v c)) ^ 2 ≤
        2 * (p a * (u a - ∑ c, p c * u c) ^ 2) + 2 * (p a * (v a - ∑ c, p c * v c) ^ 2) := by
      intro a
      simp only [Pi.add_apply]
      have h0 := hp0 a
      nlinarith [mul_nonneg h0 (sq_nonneg ((u a - ∑ c, p c * u c) - (v a - ∑ c, p c * v c)))]
    calc ∑ a, p a * ((u + v) a - (∑ c, p c * u c + ∑ c, p c * v c)) ^ 2
        ≤ ∑ a, (2 * (p a * (u a - ∑ c, p c * u c) ^ 2) +
            2 * (p a * (v a - ∑ c, p c * v c) ^ 2)) := Finset.sum_le_sum (fun a _ => h a)
      _ = 2 * var p u + 2 * var p v := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
        try rfl
  · refine (var_le_center p v hp1 (lo + b / 2)).trans ?_
    have : ∑ a, p a * (v a - (lo + b / 2)) ^ 2 ≤ ∑ a, p a * (b ^ 2 / 4) := by
      refine Finset.sum_le_sum (fun a _ => ?_)
      apply mul_le_mul_of_nonneg_left _ (hp0 a)
      obtain ⟨h1, h2⟩ := hb a
      nlinarith [mul_nonneg (sub_nonneg.mpr h1) (sub_nonneg.mpr h2)]
    rw [← Finset.sum_mul, hp1, one_mul] at this
    exact this
  · refine (var_le_center p v hp1 0).trans ?_
    have : ∑ a, p a * (v a - 0) ^ 2 ≤ ∑ a, p a * ‖v‖ ^ 2 := by
      refine Finset.sum_le_sum (fun a _ => ?_)
      apply mul_le_mul_of_nonneg_left _ (hp0 a)
      rw [sub_zero, ← sq_abs]
      have h := norm_le_pi_norm v a
      rw [Real.norm_eq_abs] at h
      exact pow_le_pow_left₀ (abs_nonneg _) h 2
    rw [← Finset.sum_mul, hp1, one_mul] at this
    exact this
