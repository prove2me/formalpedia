-- Prove2me | solution 1 for Sherlocking.InfoPolicy.oc0_iff_ineq4
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-30T09:25:10.758266+00:00
-- url     : https://prove2.me/submissions/9d3f984a-dc57-4f55-8650-778734dec3d7

import Mathlib
import Definitions.Def_Sherlocking_InfoPolicy_Model

open MeasureTheory Sherlocking.InfoPolicy

namespace SherlockAux

lemma ivl_int_of_bdd {f : ℝ → ℝ} (hf : Measurable f) (M : ℝ) (hM : ∀ x, |f x| ≤ M) (a b : ℝ) :
    IntervalIntegrable f volume a b := by
  rw [intervalIntegrable_iff]
  exact Measure.integrableOn_of_bounded (M := M) (by rw [Set.uIoc]; exact measure_Ioc_lt_top.ne)
    hf.aestronglyMeasurable (Filter.Eventually.of_forall (fun x => by simpa using hM x))

lemma meas_alpha (K δ r : ℝ) : Measurable (fun θ => alpha K δ θ r) := by
  unfold alpha; fun_prop

lemma meas_c (K δ r : ℝ) : Measurable (commitProb K δ r) := by
  unfold commitProb
  exact Measurable.ite (measurableSet_Icc (a := thetaP K δ r) (b := 1)) (meas_alpha K δ r)
    measurable_const

structure Facts (K δ r : ℝ) : Prop where
  hK0 : 0 < K
  hδ0 : 0 < δ
  hδ1 : δ < 1
  hr0 : 0 ≤ r
  hrK : r < 1 - K
  hS : thetaS K r = K / (1 - r)
  hS0 : 0 < thetaS K r
  hSP : thetaS K r < thetaP K δ r
  hP1 : thetaP K δ r ≤ 1
  hα : ∀ θ ∈ Set.Icc (thetaP K δ r) 1, 0 ≤ alpha K δ θ r ∧ alpha K δ θ r < 1

lemma facts (K δ r : ℝ) (hδ1 : δ < 1) (hK1 : 1 - δ < K) (hK2 : K < δ) (hr0 : 0 ≤ r)
    (hrK : r < 1 - K) : Facts K δ r := by
  have ha : K < 1 - r := by linarith
  have hK0 : 0 < K := by linarith
  have hδ0 : 0 < δ := by linarith
  have hapos : 0 < 1 - r := by linarith
  have hS : thetaS K r = K / (1 - r) := by unfold thetaS; rw [if_pos ha]
  have hSle1 : K / (1 - r) < 1 := (div_lt_one hapos).mpr ha
  have hS0 : 0 < K / (1 - r) := div_pos hK0 hapos
  have hP_ge : K / (1 - r) < thetaP K δ r := by
    unfold thetaP
    split_ifs with h
    · rw [div_lt_div_iff₀ hapos (by positivity)]
      have := mul_pos (mul_pos hK0 hapos) (sub_pos.mpr hδ1)
      nlinarith
    · linarith
  have hP_le1 : thetaP K δ r ≤ 1 := by
    unfold thetaP
    split_ifs with h
    · exact (div_le_one (by positivity)).mpr h.le
    · exact le_refl _
  refine ⟨hK0, hδ0, hδ1, hr0, hrK, hS, by rw [hS]; exact hS0, by rw [hS]; exact hP_ge,
    hP_le1, ?_⟩
  intro θ hθ
  obtain ⟨hθ1, hθ2⟩ := hθ
  have hθS : K / (1 - r) ≤ θ := hP_ge.le.trans hθ1
  have hθ0 : 0 < θ := lt_of_lt_of_le hS0 hθS
  have hD : 0 < (1 - r) * θ := mul_pos hapos hθ0
  have hKD : K ≤ (1 - r) * θ := by
    rw [div_le_iff₀ hapos] at hθS; linarith
  have h1 : K / ((1 - r) * θ) ≤ 1 := (div_le_one hD).mpr hKD
  have hDle : (1 - r) * θ ≤ 1 := by nlinarith
  have h2 : 1 - δ < K / ((1 - r) * θ) := by
    rw [lt_div_iff₀ hD]; nlinarith
  unfold alpha
  constructor
  · apply mul_nonneg (by positivity); linarith
  · have e : 1 / δ * (1 - K / ((1 - r) * θ)) = (1 - K / ((1 - r) * θ)) / δ := by ring
    rw [e, div_lt_one hδ0]
    linarith

variable {K δ r : ℝ}

lemma Facts.c_bounds (F : Facts K δ r) (θ : ℝ) : 0 ≤ commitProb K δ r θ ∧ commitProb K δ r θ < 1 := by
  unfold commitProb
  split_ifs with h
  · exact F.hα θ h
  · exact ⟨le_refl _, one_pos⟩

lemma Facts.c_zero (F : Facts K δ r) {θ : ℝ} (h : θ < thetaP K δ r) : commitProb K δ r θ = 0 := by
  unfold commitProb; rw [if_neg]; intro h'; linarith [h'.1]

lemma Facts.c_alpha (F : Facts K δ r) {θ : ℝ} (h1 : thetaP K δ r ≤ θ) (h2 : θ ≤ 1) :
    commitProb K δ r θ = alpha K δ θ r := by
  unfold commitProb; rw [if_pos ⟨h1, h2⟩]

lemma Facts.c_abs (F : Facts K δ r) (θ : ℝ) : |commitProb K δ r θ| ≤ 1 := by
  have := F.c_bounds θ; rw [abs_le]; constructor <;> linarith

/-- Interval integrability of `f θ * (1 - c θ)` for `f` continuous. -/
lemma Facts.ii_mul (F : Facts K δ r) {f : ℝ → ℝ} (hf : Continuous f) (a b : ℝ) :
    IntervalIntegrable (fun θ => f θ * (1 - commitProb K δ r θ)) volume a b := by
  have h1 : IntervalIntegrable (fun θ => 1 - commitProb K δ r θ) volume a b :=
    ivl_int_of_bdd (by have := meas_c K δ r; fun_prop) 1
      (fun θ => by have := F.c_bounds θ; rw [abs_le]; constructor <;> linarith) a b
  exact h1.continuousOn_mul hf.continuousOn

/-- `Φ = ∫_{θS}^1 (θ - θP)(1 - c)`; OC0 ⇔ Φ ≤ 0. -/
lemma Facts.oc0_iff (F : Facts K δ r) :
    OC0 K δ r ↔ (∫ θ in (thetaS K r)..1, (θ - thetaP K δ r) * (1 - commitProb K δ r θ)) ≤ 0 := by
  unfold OC0
  have hSP := F.hSP
  have hS1 : thetaS K r < 1 := lt_of_lt_of_le hSP F.hP1
  have iD := F.ii_mul (f := fun _ => (1:ℝ)) continuous_const (thetaS K r) 1
  have iN := F.ii_mul (f := fun θ => θ) continuous_id (thetaS K r) 1
  simp only [one_mul] at iD
  have hD : 0 < ∫ θ in (thetaS K r)..1, (1 - commitProb K δ r θ) := by
    apply intervalIntegral.intervalIntegral_pos_of_pos_on iD _ hS1
    intro x _; have := F.c_bounds x; linarith
  rw [div_le_iff₀ hD]
  have e : (∫ θ in (thetaS K r)..1, (θ - thetaP K δ r) * (1 - commitProb K δ r θ)) =
      (∫ θ in (thetaS K r)..1, θ * (1 - commitProb K δ r θ)) -
        thetaP K δ r * ∫ θ in (thetaS K r)..1, (1 - commitProb K δ r θ) := by
    rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_sub iN (iD.const_mul _)]
    congr 1; ext θ; ring
  rw [e, mul_comm]; constructor <;> intro h <;> linarith

lemma Facts.phi_split (F : Facts K δ r) :
    (∫ θ in (thetaS K r)..1, (θ - thetaP K δ r) * (1 - commitProb K δ r θ)) =
      (∫ θ in (thetaP K δ r)..1, (θ - thetaP K δ r) * (1 - alpha K δ θ r)) -
        ∫ θ in (thetaS K r)..(thetaP K δ r), (thetaP K δ r - θ) := by
  have hcont : Continuous (fun θ : ℝ => θ - thetaP K δ r) := by fun_prop
  rw [← intervalIntegral.integral_add_adjacent_intervals (F.ii_mul hcont _ (thetaP K δ r))
    (F.ii_mul hcont _ _)]
  have e1 : (∫ θ in (thetaS K r)..(thetaP K δ r), (θ - thetaP K δ r) * (1 - commitProb K δ r θ))
      = -∫ θ in (thetaS K r)..(thetaP K δ r), (thetaP K δ r - θ) := by
    rw [← intervalIntegral.integral_neg]
    apply intervalIntegral.integral_congr
    intro θ hθ
    rw [Set.uIcc_of_le F.hSP.le] at hθ
    rcases eq_or_lt_of_le hθ.2 with h | h
    · simp [h]
    · simp only [F.c_zero h]; ring
  have e2 : (∫ θ in (thetaP K δ r)..1, (θ - thetaP K δ r) * (1 - commitProb K δ r θ))
      = ∫ θ in (thetaP K δ r)..1, (θ - thetaP K δ r) * (1 - alpha K δ θ r) := by
    apply intervalIntegral.integral_congr
    intro θ hθ
    rw [Set.uIcc_of_le F.hP1] at hθ
    simp only [F.c_alpha hθ.1 hθ.2]
  rw [e1, e2]; ring

lemma Facts.oc0_iff_ineq4 (F : Facts K δ r) : OC0 K δ r ↔ Ineq4 K δ r := by
  rw [F.oc0_iff, F.phi_split]; unfold Ineq4; constructor <;> intro h <;> linarith

end SherlockAux

open SherlockAux in
theorem solution (K δ r : ℝ) (hδ1 : δ < 1) (hK1 : 1 - δ < K) (hK2 : K < δ) (hr0 : 0 ≤ r)
    (hrK : r < 1 - K) : OC0 K δ r ↔ Ineq4 K δ r :=
  (facts K δ r hδ1 hK1 hK2 hr0 hrK).oc0_iff_ineq4
