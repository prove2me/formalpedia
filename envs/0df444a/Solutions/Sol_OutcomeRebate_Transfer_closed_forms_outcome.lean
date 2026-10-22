-- Prove2me | solution 1 for OutcomeRebate.Transfer.closed_forms_outcome
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-21T20:41:18.244429+00:00
-- url     : https://prove2.me/submissions/4e3d9d00-3511-45fe-b60c-d7c89081a450

import Mathlib
import Definitions.Def_OutcomeRebate_Transfer_Model
import Theorems.Thm_OutcomeRebate_Transfer_purchase_rule_outcome

namespace OutcomeRebate.Transfer
open MeasureTheory

alias obp_purchase_rule_outcome := purchase_rule_outcome

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

lemma obp_set_integral' (a b x q : ℝ) :
    ∫ v in Set.Icc a b, q * (v - x) = max (b - a) 0 * (q * (a + b) / 2 - q * x) := by
  have := obp_set_integral a b (q * x) q
  rw [← this]
  congr 1
  funext v; ring

lemma obp_buyersO (P : Params) (hS : P.Standing) (bb p : ℝ)
    (hbb : bb = P.β ∨ bb = 1) (hp : 0 ≤ p) :
    buyersO P bb p = Set.Icc (bb * p) P.vbar := by
  have hbbpos : 0 < bb := by
    rcases hbb with h | h <;> rw [h]
    · exact hS.2.2.2.1
    · norm_num
  have h0 : 0 ≤ bb * p := mul_nonneg hbbpos.le hp
  ext v
  simp only [buyersO, Set.mem_ofPred_eq, Set.mem_Icc]
  constructor
  · rintro ⟨⟨hv0, hv1⟩, hw⟩
    exact ⟨(obp_purchase_rule_outcome P hS bb p v hbb hp hv0).mp hw, hv1⟩
  · rintro ⟨hv0, hv1⟩
    exact ⟨⟨by linarith, hv1⟩,
      (obp_purchase_rule_outcome P hS bb p v hbb hp (by linarith)).mpr hv0⟩

theorem obp_closed_forms_outcome (P : Params) (hS : P.Standing) (bb p : ℝ)
    (hbb : bb = P.β ∨ bb = 1) (hp : 0 ≤ p) :
    demandO P bb p = P.n / P.vbar * max (P.vbar - bb * p) 0 ∧
      payerObjO P bb p = P.n * P.q / P.vbar * max (P.vbar - bb * p) 0 *
        (P.vp - p + (P.vbar + bb * p) / 2) := by
  have hB := obp_buyersO P hS bb p hbb hp
  have hD : demandO P bb p = P.n / P.vbar * max (P.vbar - bb * p) 0 := by
    rw [demandO, hB, Real.volume_Icc, ENNReal.toReal_ofReal']
  refine ⟨hD, ?_⟩
  rw [payerObjO, payerPayoffO, patientPayoffO, hD, hB, obp_set_integral']
  ring


end OutcomeRebate.Transfer

open OutcomeRebate.Transfer

theorem solution (P : Params) (hS : P.Standing) (bb p : ℝ)
    (hbb : bb = P.β ∨ bb = 1) (hp : 0 ≤ p) :
    demandO P bb p = P.n / P.vbar * max (P.vbar - bb * p) 0 ∧
      payerObjO P bb p = P.n * P.q / P.vbar * max (P.vbar - bb * p) 0 *
        (P.vp - p + (P.vbar + bb * p) / 2) :=
  obp_closed_forms_outcome P hS bb p hbb hp
