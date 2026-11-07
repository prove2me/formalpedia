-- Prove2me | solution 1 for WolffPASTA.Main.eq_7
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-06T11:13:29.818219+00:00
-- url     : https://prove2.me/submissions/40d6da70-75cb-438b-86fe-8eb7c40c1b25

import Mathlib
import Definitions.Def_WolffPASTA_Main_Setting

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal Nat

namespace WolffPASTAAux


lemma pois_term_succ (r : ℝ) (n : ℕ) :
    Real.exp (-r) * r ^ (n + 1) / ((n + 1)! : ℝ) * ((n + 1 : ℕ) : ℝ)
      = r * (Real.exp (-r) * r ^ n / (n ! : ℝ)) := by
  rw [Nat.factorial_succ]
  push_cast
  have : (n ! : ℝ) ≠ 0 := by positivity
  field_simp
  ring

lemma hasSum_pois_mean (r : ℝ≥0) :
    HasSum (fun n : ℕ => Real.exp (-(r:ℝ)) * (r:ℝ) ^ n / (n ! : ℝ) * (n : ℝ)) (r : ℝ) := by
  rw [← hasSum_nat_add_iff' 1]
  simp only [Finset.range_one, Finset.sum_singleton, Nat.cast_zero, mul_zero, sub_zero]
  have h := (hasSum_one_poissonMeasure r).mul_left (r : ℝ)
  rw [mul_one] at h
  refine h.congr_fun (fun n => ?_)
  exact pois_term_succ r n

lemma hasSum_pois_sq (r : ℝ≥0) :
    HasSum (fun n : ℕ => Real.exp (-(r:ℝ)) * (r:ℝ) ^ n / (n ! : ℝ) * (n : ℝ) ^ 2)
      ((r : ℝ) + (r : ℝ) ^ 2) := by
  rw [← hasSum_nat_add_iff' 1]
  have h := ((hasSum_pois_mean r).add (hasSum_one_poissonMeasure r)).mul_left (r : ℝ)
  have key : (fun n : ℕ => Real.exp (-(r:ℝ)) * (r:ℝ) ^ (n + 1) / ((n + 1) ! : ℝ)
      * (((n + 1 : ℕ) : ℝ)) ^ 2) = fun i : ℕ => (r:ℝ) * (Real.exp (-(r:ℝ)) * (r:ℝ) ^ i / (i ! : ℝ)
        * (i : ℝ) + Real.exp (-(r:ℝ)) * (r:ℝ) ^ i / (i ! : ℝ)) := by
    funext n
    have e := pois_term_succ (r:ℝ) n
    rw [pow_two, ← mul_assoc, e]
    push_cast
    ring
  have hv : (r:ℝ) + (r:ℝ) ^ 2 - ∑ i ∈ Finset.range 1,
      Real.exp (-(r:ℝ)) * (r:ℝ) ^ i / (i ! : ℝ) * (i : ℝ) ^ 2 = (r:ℝ) * ((r:ℝ) + 1) := by
    simp; ring
  rw [hv, key]
  exact h


lemma pois_integral_id (r : ℝ≥0) :
    Integrable (fun n : ℕ => (n : ℝ)) (poissonMeasure r) ∧
      ∫ n, (n : ℝ) ∂(poissonMeasure r) = r := by
  constructor
  · rw [integrable_poissonMeasure_iff]
    simpa [Real.norm_eq_abs] using (hasSum_pois_mean r).summable
  · rw [integral_poissonMeasure]
    simpa [smul_eq_mul] using (hasSum_pois_mean r).tsum_eq

lemma pois_integral_sq (r : ℝ≥0) :
    Integrable (fun n : ℕ => (n : ℝ) ^ 2) (poissonMeasure r) ∧
      ∫ n, (n : ℝ) ^ 2 ∂(poissonMeasure r) = r + (r : ℝ) ^ 2 := by
  constructor
  · rw [integrable_poissonMeasure_iff]
    simpa [Real.norm_eq_abs] using (hasSum_pois_sq r).summable
  · rw [integral_poissonMeasure]
    simpa [smul_eq_mul] using (hasSum_pois_sq r).tsum_eq

end WolffPASTAAux

open WolffPASTA.Main WolffPASTAAux

theorem solution
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (A : ℝ → Ω → ℕ) (lam : ℝ) (hlam : 0 < lam) (hA : IsPoissonProcess P A lam)
    (U : ℝ → Ω → ℝ) (hU : ∀ s ω, 0 ≤ s → 0 ≤ U s ω ∧ U s ω ≤ 1)
    (t : ℝ) (ht : 0 ≤ t) :
    ∫⁻ ω, ENNReal.ofReal (R U A lam t ω ^ 2) ∂P ≤
      ENNReal.ofReal (lam * t + 2 * lam ^ 2 * t ^ 2) := by
  have hP : IsPoissonProcessWithIntensity P A (fun _ => lam) := hA
  have hAt : (fun ω => A t ω - A 0 ω) = A t := by
    funext ω; simp [hP.zero ω]
  have hlaw : P.map (A t) = poissonMeasure (lam * t).toNNReal := by
    have := hP.law 0 t le_rfl ht
    rw [hAt] at this
    simpa [intervalIntegral.integral_const, mul_comm] using this
  have hAm : Measurable (A t) := hP.meas t
  have hg : Measurable (fun n : ℕ => (n : ℝ) ^ 2) := measurable_from_nat
  have hint : Integrable (fun ω => (A t ω : ℝ) ^ 2) P := by
    have h1 := (pois_integral_sq (lam * t).toNNReal).1
    rw [← hlaw] at h1
    exact (integrable_map_measure h1.aestronglyMeasurable hAm.aemeasurable).mp h1
  have hval : ∫ ω, (A t ω : ℝ) ^ 2 ∂P = lam * t + (lam * t) ^ 2 := by
    have h1 := (pois_integral_sq (lam * t).toNNReal).2
    rw [← hlaw, integral_map hAm.aemeasurable hg.aestronglyMeasurable] at h1
    rw [h1, Real.coe_toNNReal _ (by positivity)]
  -- pointwise bound
  have hT : ∀ k ω, 0 ≤ T A k ω := fun k ω => Real.sInf_nonneg (fun x hx => hx.1)
  have hpt : ∀ ω, R U A lam t ω ^ 2 ≤ (A t ω : ℝ) ^ 2 + lam ^ 2 * t ^ 2 := by
    intro ω
    have hY0 : 0 ≤ Y U A t ω :=
      Finset.sum_nonneg (fun k _ => (hU _ ω (hT k ω)).1)
    have hY1 : Y U A t ω ≤ (A t ω : ℝ) := by
      have : Y U A t ω ≤ ∑ k ∈ Finset.Icc 1 (A t ω), (1 : ℝ) :=
        Finset.sum_le_sum (fun k _ => (hU _ ω (hT k ω)).2)
      simpa using this
    have hI0 : 0 ≤ ∫ s in (0:ℝ)..t, U s ω :=
      intervalIntegral.integral_nonneg ht (fun u hu => (hU u ω hu.1).1)
    have hI1 : ∫ s in (0:ℝ)..t, U s ω ≤ t := by
      by_cases hi : IntervalIntegrable (fun s => U s ω) MeasureSpace.volume 0 t
      · have := intervalIntegral.integral_mono_on ht hi intervalIntegrable_const
          (fun u hu => (hU u ω hu.1).2)
        simpa using this
      · rw [intervalIntegral.integral_undef hi]; exact ht
    have htV : t * V U t ω = ∫ s in (0:ℝ)..t, U s ω := by
      simp only [V]
      rcases ht.lt_or_eq with ht' | ht'
      · field_simp
      · subst ht'; simp
    have hR : R U A lam t ω = Y U A t ω - lam * ∫ s in (0:ℝ)..t, U s ω := by
      simp only [R]; rw [mul_assoc, htV]
    rw [hR]
    set y := Y U A t ω
    set I := ∫ s in (0:ℝ)..t, U s ω
    have h1 : 0 ≤ lam * I := mul_nonneg hlam.le hI0
    have h2 : lam * I ≤ lam * t := mul_le_mul_of_nonneg_left hI1 hlam.le
    have h3 : (lam * I) ^ 2 ≤ lam ^ 2 * t ^ 2 := by
      rw [← mul_pow]; exact pow_le_pow_left₀ h1 h2 2
    have h4 : y ^ 2 ≤ (A t ω : ℝ) ^ 2 := pow_le_pow_left₀ hY0 hY1 2
    nlinarith [mul_nonneg hY0 h1]
  calc ∫⁻ ω, ENNReal.ofReal (R U A lam t ω ^ 2) ∂P
      ≤ ∫⁻ ω, ENNReal.ofReal ((A t ω : ℝ) ^ 2 + lam ^ 2 * t ^ 2) ∂P :=
        lintegral_mono (fun ω => ENNReal.ofReal_le_ofReal (hpt ω))
    _ = ENNReal.ofReal (∫ ω, ((A t ω : ℝ) ^ 2 + lam ^ 2 * t ^ 2) ∂P) :=
        (ofReal_integral_eq_lintegral_ofReal (hint.add (integrable_const _))
          (Eventually.of_forall (fun ω => by show (0:ℝ) ≤ (A t ω : ℝ) ^ 2 + lam ^ 2 * t ^ 2; positivity))).symm
    _ = ENNReal.ofReal (lam * t + 2 * lam ^ 2 * t ^ 2) := by
        rw [integral_add hint (integrable_const _), hval]
        simp
        ring_nf
