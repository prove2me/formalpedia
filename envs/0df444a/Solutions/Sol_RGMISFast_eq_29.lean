-- Prove2me | solution 1 for RGMISFast.eq_29
-- status  : ACCEPTED   (prove)
-- author  : @srikkanthr
-- created : 2026-11-15T23:13:53.475201+00:00
-- url     : https://prove2.me/submissions/161a1a2d-5a73-4504-9440-42d89d5be6d6

import Theorems.Thm_RGMISFast_conditional_bad_event_weighted_bound
import Theorems.Thm_RGMISFast_conditional_rank_charge_laplace
import Mathlib
import Definitions.Def_RGMISFast_Gamma
import Definitions.Def_RGMISFast_gammaA
import Definitions.Def_RGMISFast_condLaw

set_option autoImplicit false

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open RGMISFast

lemma condLaw_probability {V : Type*} [Fintype V] [LinearOrder V]
    (r₀ : V → ℝ) (θ : ℝ) (A : Finset V) (rA : V → ℝ) :
    IsProbabilityMeasure (condLaw r₀ θ A rA) := by
  have : IsProbabilityMeasure (expMeasure (1:ℝ)) :=
    isProbabilityMeasure_expMeasure (by norm_num)
  have : IsProbabilityMeasure ((expMeasure (1:ℝ)).map (fun x => θ+x)) :=
    Measure.isProbabilityMeasure_map (by fun_prop)
  unfold condLaw
  have : ∀ v : V, IsProbabilityMeasure
      (if r₀ v < θ then Measure.dirac (r₀ v)
       else if v ∈ A then Measure.dirac (rA v) else (expMeasure 1).map (fun x => θ+x)) := by
    intro v
    split_ifs <;> infer_instance
  infer_instance

lemma eq29_am_positive (m : ℕ) : 0 < am m := by
  unfold am a0 c
  positivity

theorem solution {V : Type*} [Fintype V] [LinearOrder V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (u : V) (L : ℝ) (hL : 8 ≤ L) (m : ℕ) (hm : 1 ≤ m) (r₀ : V → ℝ)
    (hr₀ : IsHistory r₀ (am m / 2)) (A : Finset V) (hA : IsRootConnected G u A) :
    (condLaw r₀ (am m / 2) ∅ (fun _ => 0)
        {r | 2 * S r A (am m) + L < ((GammaAB G r (am m) ((c * am m : ℝ) : WithTop ℝ) A).card : ℝ)} ≤
          (if ActiveAt G r₀ (am m / 2) A then 1 else 0) *
            condLaw r₀ (am m / 2) ∅ (fun _ => 0) {r | ∀ v ∈ A, am m ≤ r v} *
              ENNReal.ofReal (Real.exp (-L) * gammaA (am m) ^ A.card) ∧
      (if ActiveAt G r₀ (am m / 2) A then 1 else 0) *
            condLaw r₀ (am m / 2) ∅ (fun _ => 0) {r | ∀ v ∈ A, am m ≤ r v} *
              ENNReal.ofReal (Real.exp (-L) * gammaA (am m) ^ A.card) ≤
          (if ActiveAt G r₀ (am m / 2) A then 1 else 0) *
            ENNReal.ofReal (Real.exp (-L) * gammaA (am m) ^ A.card)) ∧
    ∀ i : ℕ, i < m →
      condLaw r₀ (am m / 2) ∅ (fun _ => 0)
          {r | 32 * c ^ (1 + m - i) * (2 * S r A (am m) + L) < (Kmi G r m i A : ℝ)} ≤
            (if ActiveAt G r₀ (am m / 2) A then 1 else 0) *
              condLaw r₀ (am m / 2) ∅ (fun _ => 0) {r | ∀ v ∈ A, am m ≤ r v} *
                ENNReal.ofReal (Real.exp (-L) * gammaA (am m) ^ A.card) ∧
        (if ActiveAt G r₀ (am m / 2) A then 1 else 0) *
              condLaw r₀ (am m / 2) ∅ (fun _ => 0) {r | ∀ v ∈ A, am m ≤ r v} *
                ENNReal.ofReal (Real.exp (-L) * gammaA (am m) ^ A.card) ≤
            (if ActiveAt G r₀ (am m / 2) A then 1 else 0) *
              ENNReal.ofReal (Real.exp (-L) * gammaA (am m) ^ A.card) := by
  have hpos := eq29_am_positive m
  have hweighted := conditional_bad_event_weighted_bound G u L hL m hm r₀ hr₀ A hA
  have hlap := conditional_rank_charge_laplace r₀ (am m / 2) (am m) L hpos (by linarith) A
  rw [hlap] at hweighted
  haveI := condLaw_probability r₀ (am m / 2) ∅ (fun _ => 0)
  have hprob : condLaw r₀ (am m / 2) ∅ (fun _ => 0)
      {r | ∀ v ∈ A, am m ≤ r v} ≤ 1 := prob_le_one
  have hdrop :
      (if ActiveAt G r₀ (am m / 2) A then (1:ℝ≥0∞) else 0) *
        condLaw r₀ (am m / 2) ∅ (fun _ => 0) {r | ∀ v ∈ A, am m ≤ r v} *
          ENNReal.ofReal (Real.exp (-L) * gammaA (am m) ^ A.card) ≤
      (if ActiveAt G r₀ (am m / 2) A then (1:ℝ≥0∞) else 0) *
          ENNReal.ofReal (Real.exp (-L) * gammaA (am m) ^ A.card) := by
    calc
      _ ≤ (if ActiveAt G r₀ (am m / 2) A then (1:ℝ≥0∞) else 0) * 1 *
            ENNReal.ofReal (Real.exp (-L) * gammaA (am m) ^ A.card) :=
        mul_le_mul_left (mul_le_mul_right hprob _) _
      _ = _ := by rw [mul_one]
  exact ⟨⟨by simpa only [mul_assoc] using hweighted.1, hdrop⟩,
    fun i hi => ⟨by simpa only [mul_assoc] using hweighted.2 i hi, hdrop⟩⟩

