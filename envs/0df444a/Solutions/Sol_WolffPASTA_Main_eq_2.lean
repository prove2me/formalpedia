-- Prove2me | solution 1 for WolffPASTA.Main.eq_2
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-06T11:40:51.846194+00:00
-- url     : https://prove2.me/submissions/5e9fc52d-e72f-4807-b8d7-8134b565f48d

import Mathlib
import Definitions.Def_WolffPASTA_Main_Setting

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal Nat
open WolffPASTA.Main

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

open WolffPASTAAux

theorem solution
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {S : Type*} [MeasurableSpace S] (N : ℝ → Ω → S)
    (A : ℝ → Ω → ℕ) (lam : ℝ) (hlam : 0 < lam) (hA : IsPoissonProcess P A lam)
    (B : Set S) (hB : ∀ t, 0 ≤ t → MeasurableSet {ω | N t ω ∈ B})
    (hLAA : LAA P A (U N B))
    (n : ℕ) (hn : 1 ≤ n) (t : ℝ) (ht : 0 < t) :
    Integrable (Yn (U N B) A n t) P ∧
      ∫ ω, Yn (U N B) A n t ω ∂P =
        lam * t * ∫ ω, (∑ k ∈ Finset.range n, U N B (k * t / n) ω / n) ∂P := by
  have hP : IsPoissonProcessWithIntensity P A (fun _ => lam) := hA
  have hU : ∀ s ω, 0 ≤ s → 0 ≤ U N B s ω ∧ U N B s ω ≤ 1 := by
    intro s ω _
    simp only [U, Set.indicator]
    split_ifs <;> norm_num
  set W := U N B with hW
  have hWm : ∀ s, 0 ≤ s → Measurable (W s) := by
    intro s hs
    have : W s = Set.indicator {ω | N s ω ∈ B} (fun _ => (1:ℝ)) := by
      funext ω; simp [hW, U, Set.indicator]
    rw [this]; exact measurable_const.indicator (hB s hs)
  have hlawgen : ∀ a b, 0 ≤ a → a ≤ b →
      P.map (fun ω => A b ω - A a ω) = poissonMeasure (lam * (b - a)).toNNReal := by
    intro a b ha hab
    have := hP.law a b ha hab
    rw [intervalIntegral.integral_const, smul_eq_mul, mul_comm (b - a) lam] at this
    exact this
  have hmean : ∀ a b, 0 ≤ a → a ≤ b →
      Integrable (fun ω => ((A b ω - A a ω : ℕ) : ℝ)) P ∧
        ∫ ω, ((A b ω - A a ω : ℕ) : ℝ) ∂P = lam * (b - a) := by
    intro a b ha hab
    have hm : Measurable (fun ω => A b ω - A a ω) := (hP.meas _).sub (hP.meas _)
    have hc : Measurable (fun n : ℕ => (n : ℝ)) := measurable_from_nat
    obtain ⟨h1, h2⟩ := pois_integral_id (lam * (b - a)).toNNReal
    rw [← hlawgen a b ha hab] at h1 h2
    refine ⟨(integrable_map_measure h1.aestronglyMeasurable hm.aemeasurable).mp h1, ?_⟩
    rw [integral_map hm.aemeasurable hc.aestronglyMeasurable] at h2
    rw [show (∫ ω, ((A b ω - A a ω : ℕ) : ℝ) ∂P) = ∫ ω, (fun n : ℕ => (n:ℝ)) (A b ω - A a ω) ∂P
      from rfl, h2, Real.coe_toNNReal _ (by nlinarith)]
  have hn' : (0:ℝ) < n := by exact_mod_cast hn
  have htn : 0 < t / n := by positivity
  have hk0 : ∀ k : ℕ, (0:ℝ) ≤ k * t / n := fun k => by positivity
  have hk1 : ∀ k : ℕ, ((k:ℝ) + 1) * t / n = k * t / n + t / n := fun k => by ring
  have hcast : ∀ (k : ℕ) (ω : Ω), ((A ((k + 1) * t / n) ω : ℝ) - A (k * t / n) ω) =
      ((A (k * t / n + t / n) ω - A (k * t / n) ω : ℕ) : ℝ) := by
    intro k ω
    rw [hk1 k]
    have : A (k * t / n) ω ≤ A (k * t / n + t / n) ω := hP.mono ω (by linarith)
    rw [Nat.cast_sub this]
  have hterm_int : ∀ k : ℕ, Integrable (fun ω => W (k * t / n) ω *
      ((A ((k + 1) * t / n) ω : ℝ) - A (k * t / n) ω)) P := by
    intro k
    have hdi := (hmean (k * t / n) (k * t / n + t / n) (hk0 k) (by linarith)).1
    refine (hdi.bdd_mul (c := 1) (hWm _ (hk0 k)).aestronglyMeasurable
      (Eventually.of_forall (fun ω => ?_))).congr (Eventually.of_forall (fun ω => ?_))
    · rw [Real.norm_eq_abs, abs_of_nonneg (hU _ ω (hk0 k)).1]; exact (hU _ ω (hk0 k)).2
    · simp only; rw [hcast k ω]
  have hW_int : ∀ k : ℕ, Integrable (fun ω => W (k * t / n) ω) P := by
    intro k
    refine (integrable_const (1:ℝ)).mono' (hWm _ (hk0 k)).aestronglyMeasurable
      (Eventually.of_forall (fun ω => ?_))
    rw [Real.norm_eq_abs, abs_of_nonneg (hU _ ω (hk0 k)).1]; exact (hU _ ω (hk0 k)).2
  have hterm : ∀ k : ℕ, ∫ ω, W (k * t / n) ω *
      ((A ((k + 1) * t / n) ω : ℝ) - A (k * t / n) ω) ∂P =
      (∫ ω, W (k * t / n) ω ∂P) * (lam * (t / n)) := by
    intro k
    set s := (k:ℝ) * t / n with hs
    have hs0 : 0 ≤ s := hk0 k
    set d : Ω → ℝ := fun ω => ((A (s + t / n) ω - A s ω : ℕ) : ℝ) with hd
    have hdm : Measurable d := measurable_from_nat.comp ((hP.meas _).sub (hP.meas _))
    obtain ⟨_, hdmean⟩ := hmean s (s + t / n) hs0 (by linarith)
    rw [add_sub_cancel_left] at hdmean
    have e1 : (fun ω => W s ω * ((A ((k + 1) * t / n) ω : ℝ) - A s ω)) =
        fun ω => W s ω * d ω := by
      funext ω; rw [hcast k ω]
    rw [e1]
    have hX : Measurable[⨆ r ∈ Set.Icc (0 : ℝ) s, MeasurableSpace.comap (W r) inferInstance]
        (W s) := (comap_measurable (W s)).mono
          (le_iSup₂ (f := fun r (_ : r ∈ Set.Icc (0:ℝ) s) =>
            MeasurableSpace.comap (W r) inferInstance) s ⟨hs0, le_rfl⟩) le_rfl
    have hD : Measurable[⨆ u ∈ Set.Ici (0 : ℝ),
        MeasurableSpace.comap (fun ω => A (s + u) ω - A s ω) inferInstance] d := by
      have h1 : Measurable[MeasurableSpace.comap (fun ω => A (s + t / n) ω - A s ω)
          inferInstance] (fun ω => A (s + t / n) ω - A s ω) := comap_measurable _
      have h2 : Measurable[MeasurableSpace.comap (fun ω => A (s + t / n) ω - A s ω)
          inferInstance] d := (measurable_from_nat (f := fun m : ℕ => (m:ℝ))).comp h1
      refine h2.mono ?_ le_rfl
      exact le_iSup₂ (f := fun u (_ : u ∈ Set.Ici (0:ℝ)) =>
        MeasurableSpace.comap (fun ω => A (s + u) ω - A s ω) inferInstance) (t / n)
        (Set.mem_Ici.mpr htn.le)
    have hind : IndepFun (W s) d P := by
      rw [IndepFun_iff_Indep]
      exact indep_of_indep_of_le_left (indep_of_indep_of_le_right (hLAA s hs0).symm
        hD.comap_le) hX.comap_le
    have := hind.integral_mul_eq_mul_integral
      (hWm s hs0).aestronglyMeasurable hdm.aestronglyMeasurable
    simp only [Pi.mul_apply] at this
    rw [this, hdmean]
  have hYn : Yn W A n t = fun ω => ∑ k ∈ Finset.range n, W (k * t / n) ω *
      ((A ((k + 1) * t / n) ω : ℝ) - A (k * t / n) ω) := by
    funext ω; simp only [Yn]
  rw [hYn]
  refine ⟨integrable_finset_sum _ (fun k _ => hterm_int k), ?_⟩
  rw [integral_finset_sum _ (fun k _ => hterm_int k),
    integral_finset_sum _ (fun k _ => (hW_int k).div_const _), Finset.mul_sum]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [hterm k, integral_div]
  field_simp
