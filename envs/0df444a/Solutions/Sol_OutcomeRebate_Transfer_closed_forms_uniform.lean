-- Prove2me | solution 1 for OutcomeRebate.Transfer.closed_forms_uniform
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-21T20:41:17.551134+00:00
-- url     : https://prove2.me/submissions/17bab17c-12f3-4861-b3db-55d547749ac3

import Mathlib
import Definitions.Def_OutcomeRebate_Transfer_Model
import Theorems.Thm_OutcomeRebate_Transfer_purchase_rule_uniform

namespace OutcomeRebate.Transfer
open MeasureTheory

lemma obp_k_pos (P : Params) (hS : P.Standing) : 0 < P.lam * (1 - P.q) / P.q := by
  obtain ⟨_, _, _, _, _, hq0, hq1, _, _, hlam, _⟩ := hS
  apply div_pos _ hq0
  apply mul_pos (by linarith) (by linarith)

lemma obp_z_eq (P : Params) : P.z = 1 + (P.lam * (1 - P.q) / P.q) ^ (1 / P.α) := rfl

lemma obp_z_ge_one (P : Params) (hS : P.Standing) : 1 ≤ P.z := by
  rw [obp_z_eq]
  have := Real.rpow_nonneg (obp_k_pos P hS).le (1 / P.α)
  linarith

alias obp_purchase_rule_uniform := purchase_rule_uniform

lemma obp_set_integral (a b x q : ℝ) :
    ∫ v in Set.Icc a b, (q * (v - x) - (1 - q) * x) =
      max (b - a) 0 * (q * (a + b) / 2 - x) := by
  rcases le_or_gt a b with hab | hab
  · rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hab]
    have : (fun v : ℝ => q * (v - x) - (1 - q) * x) = fun v => q * v - x := by
      funext v; ring
    rw [this, intervalIntegral.integral_sub (f := fun v => q * v) (g := fun _ => x)
      ((continuous_const.mul continuous_id).intervalIntegrable _ _) intervalIntegrable_const,
      intervalIntegral.integral_const_mul, integral_id, intervalIntegral.integral_const,
      max_eq_left (by linarith)]
    simp only [smul_eq_mul]
    ring
  · rw [Set.Icc_eq_empty (not_le.mpr hab), Measure.restrict_empty, integral_zero_measure,
      max_eq_right (by linarith)]
    ring

lemma obp_buyersU (P : Params) (hS : P.Standing) (bb p : ℝ)
    (hbb : bb = P.β ∨ bb = 1) (hp : 0 ≤ p) :
    buyersU P bb p = Set.Icc (bb * p * P.z) P.vbar := by
  have hbbpos : 0 < bb := by
    rcases hbb with h | h <;> rw [h]
    · exact hS.2.2.2.1
    · norm_num
  have hz1 := obp_z_ge_one P hS
  have h0 : 0 ≤ bb * p * P.z := mul_nonneg (mul_nonneg hbbpos.le hp) (by linarith)
  ext v
  simp only [buyersU, Set.mem_ofPred_eq, Set.mem_Icc]
  constructor
  · rintro ⟨⟨hv0, hv1⟩, hw⟩
    exact ⟨(obp_purchase_rule_uniform P hS bb p v hbb hp hv0).mp hw, hv1⟩
  · rintro ⟨hv0, hv1⟩
    exact ⟨⟨by linarith, hv1⟩,
      (obp_purchase_rule_uniform P hS bb p v hbb hp (by linarith)).mpr hv0⟩

theorem obp_closed_forms_uniform (P : Params) (hS : P.Standing) (bb p : ℝ)
    (hbb : bb = P.β ∨ bb = 1) (hp : 0 ≤ p) :
    demandU P bb p = P.n / P.vbar * max (P.vbar - bb * p * P.z) 0 ∧
      payerObjU P bb p = P.n / P.vbar * max (P.vbar - bb * p * P.z) 0 *
        (P.q * P.vp - p + P.q / 2 * (P.vbar + bb * p * P.z)) := by
  have hB := obp_buyersU P hS bb p hbb hp
  have hD : demandU P bb p = P.n / P.vbar * max (P.vbar - bb * p * P.z) 0 := by
    rw [demandU, hB, Real.volume_Icc, ENNReal.toReal_ofReal']
  refine ⟨hD, ?_⟩
  rw [payerObjU, payerPayoffU, patientPayoffU, hD, hB, obp_set_integral]
  ring


end OutcomeRebate.Transfer

open OutcomeRebate.Transfer

theorem solution (P : Params) (hS : P.Standing) (bb p : ℝ)
    (hbb : bb = P.β ∨ bb = 1) (hp : 0 ≤ p) :
    demandU P bb p = P.n / P.vbar * max (P.vbar - bb * p * P.z) 0 ∧
      payerObjU P bb p = P.n / P.vbar * max (P.vbar - bb * p * P.z) 0 *
        (P.q * P.vp - p + P.q / 2 * (P.vbar + bb * p * P.z)) :=
  obp_closed_forms_uniform P hS bb p hbb hp
