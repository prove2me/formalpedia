-- Prove2me | solution 1 for PrivGaussMS.lemma_A_4
-- status  : ACCEPTED   (prove)
-- author  : @CGTMoyano
-- created : 2026-11-24T17:58:26.343428+00:00
-- url     : https://prove2.me/submissions/c114d5d1-708e-4eb9-8e4b-e17b5a7ec184

import Mathlib
import Definitions.Def_PrivGaussMS_Basics
import Theorems.Thm_PrivGaussMS_lemma_A_1
import Theorems.Thm_PrivGaussMS_lemma_A_2
import Theorems.Thm_PrivGaussMS_lemma_A_3

open MeasureTheory ProbabilityTheory PrivateUniformGen.Characterization

namespace SolPrivGaussMSA4

/-- The Laplace density. -/
noncomputable def lapDens (b z : ℝ) : ENNReal := ENNReal.ofReal (Real.exp (-|z| / b) / (2 * b))

lemma laplace_eq (b : ℝ) : PrivGaussMS.laplace b = volume.withDensity (lapDens b) := rfl

lemma measurable_lapDens (b : ℝ) : Measurable (lapDens b) := by
  unfold lapDens
  exact (by fun_prop : Continuous fun z : ℝ => Real.exp (-|z| / b) / (2 * b)).measurable
    |>.ennreal_ofReal

lemma lapDens_neg (b z : ℝ) : lapDens b (-z) = lapDens b z := by
  simp [lapDens, abs_neg]

/-- Tail mass of the Laplace law. -/
lemma lap_tail (b ℓ : ℝ) (hb : 0 < b) (hℓ : 0 ≤ ℓ) :
    PrivGaussMS.laplace b {z | ℓ < |z|} = ENNReal.ofReal (Real.exp (-ℓ / b)) := by
  have hS : MeasurableSet {z : ℝ | ℓ < |z|} :=
    measurableSet_lt measurable_const continuous_abs.measurable
  rw [laplace_eq, withDensity_apply _ hS, ← lintegral_indicator hS]
  have hsplit : ∀ z, {z : ℝ | ℓ < |z|}.indicator (lapDens b) z =
      (Set.Ioi ℓ).indicator (lapDens b) z + (Set.Ioi ℓ).indicator (lapDens b) (-z) := by
    intro z
    by_cases h1 : ℓ < z
    · have h2 : ¬ ℓ < -z := by linarith
      have h3 : ℓ < |z| := lt_of_lt_of_le h1 (le_abs_self z)
      rw [Set.indicator_of_mem (show z ∈ {z : ℝ | ℓ < |z|} from h3),
        Set.indicator_of_mem (show z ∈ Set.Ioi ℓ from h1),
        Set.indicator_of_notMem (show -z ∉ Set.Ioi ℓ from h2), add_zero]
    · by_cases h2 : ℓ < -z
      · have h3 : ℓ < |z| := lt_of_lt_of_le h2 (neg_le_abs z)
        rw [Set.indicator_of_mem (show z ∈ {z : ℝ | ℓ < |z|} from h3),
          Set.indicator_of_notMem (show z ∉ Set.Ioi ℓ from h1),
          Set.indicator_of_mem (show -z ∈ Set.Ioi ℓ from h2), zero_add, lapDens_neg]
      · have h3 : ¬ ℓ < |z| := by
          rw [lt_abs]; push_neg; exact ⟨not_lt.1 h1, not_lt.1 h2⟩
        rw [Set.indicator_of_notMem (show z ∉ {z : ℝ | ℓ < |z|} from h3),
          Set.indicator_of_notMem (show z ∉ Set.Ioi ℓ from h1),
          Set.indicator_of_notMem (show -z ∉ Set.Ioi ℓ from h2), add_zero]
  simp_rw [hsplit]
  have hm : Measurable ((Set.Ioi ℓ).indicator (lapDens b)) :=
    (measurable_lapDens b).indicator measurableSet_Ioi
  rw [lintegral_add_left hm,
    lintegral_neg_eq_self (fun z => (Set.Ioi ℓ).indicator (lapDens b) z), ← two_mul,
    lintegral_indicator measurableSet_Ioi]
  have hcongr : Set.EqOn (lapDens b)
      (fun z => ENNReal.ofReal (Real.exp (-1 / b * z) / (2 * b))) (Set.Ioi ℓ) := by
    intro z hz
    have hz0 : 0 < z := lt_of_le_of_lt hℓ hz
    simp only [lapDens, abs_of_pos hz0]
    congr 3
    ring
  rw [setLIntegral_congr_fun measurableSet_Ioi hcongr]
  have hneg : -1 / b < 0 := by
    have : 0 < 1 / b := by positivity
    rw [neg_div]; linarith
  have hint : IntegrableOn (fun z : ℝ => Real.exp (-1 / b * z) / (2 * b)) (Set.Ioi ℓ) :=
    (integrableOn_exp_mul_Ioi hneg ℓ).div_const _
  rw [← ofReal_integral_eq_lintegral_ofReal hint
    (Filter.Eventually.of_forall fun z => by positivity), integral_div,
    integral_exp_mul_Ioi hneg ℓ]
  rw [show (2 : ENNReal) = ENNReal.ofReal 2 by simp, ← ENNReal.ofReal_mul (by norm_num)]
  congr 1
  have hb' : b ≠ 0 := hb.ne'
  have : -1 / b * ℓ = -ℓ / b := by ring
  rw [this]
  field_simp

lemma isProb_laplace (b : ℝ) (hb : 0 < b) : IsProbabilityMeasure (PrivGaussMS.laplace b) := by
  constructor
  have h0 := lap_tail b 0 hb le_rfl
  rw [neg_zero, zero_div, Real.exp_zero, ENNReal.ofReal_one] at h0
  have hS : MeasurableSet {z : ℝ | (0 : ℝ) < |z|} :=
    measurableSet_lt measurable_const continuous_abs.measurable
  have hc : PrivGaussMS.laplace b {z : ℝ | (0 : ℝ) < |z|}ᶜ = 0 := by
    refine measure_mono_null (t := {0}) ?_ ?_
    · intro z hz
      simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_lt] at hz
      simp only [Set.mem_singleton_iff]
      exact abs_nonpos_iff.1 hz
    · rw [laplace_eq]
      exact withDensity_absolutelyContinuous _ _ (Real.volume_singleton)
  rw [← measure_add_measure_compl hS, h0, hc, add_zero]

/-- The law of `c + Z` as an integral of the shifted density. -/
lemma shift_apply (b c : ℝ) (O : Set ℝ) (hO : MeasurableSet O) :
    ((PrivGaussMS.laplace b).map fun z => c + z) O =
      ∫⁻ y, O.indicator (fun y => lapDens b (y - c)) y := by
  have hm : Measurable fun z : ℝ => c + z := measurable_const_add c
  rw [Measure.map_apply hm hO, laplace_eq, withDensity_apply _ (hm hO),
    ← lintegral_indicator (hm hO),
    ← lintegral_sub_right_eq_self (fun z => ((fun z => c + z) ⁻¹' O).indicator (lapDens b) z) c]
  congr 1
  funext y
  by_cases hy : y ∈ O
  · rw [Set.indicator_of_mem hy, Set.indicator_of_mem]
    simpa using hy
  · rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem]
    simpa using hy

lemma shift_le (b Δ c c' : ℝ) (hb : 0 < b) (hcc : |c - c'| ≤ Δ) (O : Set ℝ)
    (hO : MeasurableSet O) :
    ((PrivGaussMS.laplace b).map fun z => c + z) O ≤
      ENNReal.ofReal (Real.exp (Δ / b)) * ((PrivGaussMS.laplace b).map fun z => c' + z) O := by
  rw [shift_apply b c O hO, shift_apply b c' O hO, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_mono fun y => ?_
  by_cases hy : y ∈ O
  · rw [Set.indicator_of_mem hy, Set.indicator_of_mem hy]
    simp only [lapDens]
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le]
    apply ENNReal.ofReal_le_ofReal
    rw [← mul_div_assoc, ← Real.exp_add]
    apply div_le_div_of_nonneg_right _ (by positivity)
    apply Real.exp_le_exp.2
    rw [← add_div]
    apply div_le_div_of_nonneg_right _ hb.le
    have := abs_sub_le y c c'
    linarith
  · rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem hy, mul_zero]

lemma clip_eq (ℓ z : ℝ) (h : |z| ≤ ℓ) : PrivGaussMS.clip ℓ z = z := by
  unfold PrivGaussMS.clip
  rw [abs_le] at h
  rw [min_eq_left h.2, max_eq_right h.1]

lemma measurable_clip (ℓ : ℝ) : Measurable (PrivGaussMS.clip ℓ) := by
  unfold PrivGaussMS.clip
  exact (continuous_const.max (continuous_id.min continuous_const)).measurable

end SolPrivGaussMSA4

open SolPrivGaussMSA4 in
theorem solution {X : Type*} {n : ℕ} (g : (Fin n → X) → ℝ) (Δ b : ℝ) (hΔ : 0 ≤ Δ)
    (hb : 0 < b) (hg : ∀ x x', Neighbors x x' → |g x - g x'| ≤ Δ) :
    PrivGaussMS.IsDPM (fun x => (PrivGaussMS.laplace b).map fun z => g x + z) (Δ / b) 0 ∧
    (∀ ℓ : ℝ, 0 ≤ ℓ → (PrivGaussMS.laplace b).real {z | ℓ < |z|} = Real.exp (-ℓ / b)) ∧
    (∀ ℓ : ℝ, 0 ≤ ℓ → PrivGaussMS.IsDPM
      (fun x => (PrivGaussMS.laplace b).map fun z => g x + PrivGaussMS.clip ℓ z) (Δ / b)
      ((1 + Real.exp (Δ / b)) * Real.exp (-ℓ / b))) ∧
    (∀ K : Kernel ℝ Bool, IsMarkovKernel K →
      PrivGaussMS.IsDPM (fun x => ((PrivGaussMS.laplace b).map fun z => g x + z).bind K)
        (Δ / b) 0 ∧
      ∀ ℓ : ℝ, 0 ≤ ℓ → PrivGaussMS.IsDPM
        (fun x => ((PrivGaussMS.laplace b).map fun z => g x + PrivGaussMS.clip ℓ z).bind K)
        (Δ / b) ((1 + Real.exp (Δ / b)) * Real.exp (-ℓ / b))) := by
  haveI := isProb_laplace b hb
  have hε : 0 ≤ Δ / b := div_nonneg hΔ hb.le
  -- part 1
  have part1 : PrivGaussMS.IsDPM (fun x => (PrivGaussMS.laplace b).map fun z => g x + z)
      (Δ / b) 0 := by
    refine ⟨fun x => Measure.isProbabilityMeasure_map (measurable_const_add _).aemeasurable,
      fun S S' hS O hO => ?_⟩
    show ((PrivGaussMS.laplace b).map fun z => g S + z).real O ≤
      Real.exp (Δ / b) * ((PrivGaussMS.laplace b).map fun z => g S' + z).real O + 0
    have key := shift_le b Δ (g S) (g S') hb (hg S S' hS) O hO
    have := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _)) key
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.exp_pos _).le] at this
    simpa only [measureReal_def, add_zero] using this
  -- part 2
  have part2 : ∀ ℓ : ℝ, 0 ≤ ℓ →
      (PrivGaussMS.laplace b).real {z | ℓ < |z|} = Real.exp (-ℓ / b) := by
    intro ℓ hℓ
    rw [measureReal_def, lap_tail b ℓ hb hℓ, ENNReal.toReal_ofReal (Real.exp_pos _).le]
  -- part 3
  have part3 : ∀ ℓ : ℝ, 0 ≤ ℓ → PrivGaussMS.IsDPM
      (fun x => (PrivGaussMS.laplace b).map fun z => g x + PrivGaussMS.clip ℓ z) (Δ / b)
      ((1 + Real.exp (Δ / b)) * Real.exp (-ℓ / b)) := by
    intro ℓ hℓ
    have hprob : ∀ x, IsProbabilityMeasure
        ((PrivGaussMS.laplace b).map fun z => g x + PrivGaussMS.clip ℓ z) := fun x =>
      Measure.isProbabilityMeasure_map ((measurable_clip ℓ).const_add (g x)).aemeasurable
    have htv : ∀ x, FoundationsRL.DECLower.tvDist
        ((PrivGaussMS.laplace b).map fun z => g x + z)
        ((PrivGaussMS.laplace b).map fun z => g x + PrivGaussMS.clip ℓ z) ≤
          Real.exp (-ℓ / b) := by
      intro x
      haveI : IsProbabilityMeasure ((PrivGaussMS.laplace b).map fun z => g x + z) :=
        Measure.isProbabilityMeasure_map (measurable_const_add _).aemeasurable
      haveI := hprob x
      have hpair : Measurable fun z : ℝ => (g x + z, g x + PrivGaussMS.clip ℓ z) :=
        (measurable_const_add _).prodMk ((measurable_clip ℓ).const_add (g x))
      set γ := (PrivGaussMS.laplace b).map fun z : ℝ => (g x + z, g x + PrivGaussMS.clip ℓ z)
      have h1 : γ.map Prod.fst = (PrivGaussMS.laplace b).map fun z => g x + z := by
        rw [Measure.map_map measurable_fst hpair]; rfl
      have h2 : γ.map Prod.snd =
          (PrivGaussMS.laplace b).map fun z => g x + PrivGaussMS.clip ℓ z := by
        rw [Measure.map_map measurable_snd hpair]; rfl
      have hA1 := (PrivGaussMS.lemma_A_1 (β := Bool) measurableSet_diagonal _ _).1 γ h1 h2
      refine le_trans hA1 ?_
      have hD : MeasurableSet {p : ℝ × ℝ | p.1 ≠ p.2} := measurableSet_diagonal.compl
      rw [measureReal_def, Measure.map_apply hpair hD, ← part2 ℓ hℓ, measureReal_def]
      apply ENNReal.toReal_mono (measure_ne_top _ _)
      apply measure_mono
      intro z hz
      simp only [Set.mem_preimage, Set.mem_setOf_eq] at hz ⊢
      by_contra hcon
      exact hz (by rw [clip_eq ℓ z (not_lt.1 hcon)])
    have := (PrivGaussMS.lemma_A_3 (Ω := ℝ) (X := X) (Y := ℝ) (n := n) (Δ / b) hε).2.1
      (fun x => (PrivGaussMS.laplace b).map fun z => g x + z)
      (fun x => (PrivGaussMS.laplace b).map fun z => g x + PrivGaussMS.clip ℓ z)
      0 (Real.exp (-ℓ / b)) le_rfl part1 hprob htv
    simpa only [zero_add] using this
  refine ⟨part1, part2, part3, fun K hK => ?_⟩
  haveI := hK
  have post : ∀ (M : (Fin n → X) → Measure ℝ) (δ : ℝ), 0 ≤ δ → PrivGaussMS.IsDPM M (Δ / b) δ →
      PrivGaussMS.IsDPM (fun x => (M x).bind K) (Δ / b) δ := fun M δ hδ hM =>
    (PrivGaussMS.lemma_A_2 M K M (fun _ => K) (Δ / b) δ (Δ / b) δ (Δ / b) δ hε hδ hε hδ hε hδ).1 hM
  exact ⟨post _ 0 le_rfl part1, fun ℓ hℓ => post _ _ (by positivity) (part3 ℓ hℓ)⟩
