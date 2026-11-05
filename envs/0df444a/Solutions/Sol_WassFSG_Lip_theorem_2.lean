-- Prove2me | solution 1 for WassFSG.Lip.theorem_2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-04T09:00:13.125069+00:00
-- url     : https://prove2.me/submissions/44d6e110-b9b6-4c32-a802-dd5e2be4e3b3
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_RWPI_SqrtLasso_transportCost
import Definitions.Def_ModelRiskOT_Duality_extIntegral
import Definitions.Def_WassFSG_Lip_Setting
import Definitions.Def_WassFSG_Lip_Rademacher
import Theorems.Thm_WassFSG_Lip_lemma_12

open MeasureTheory

namespace WassFSGT2Aux

set_option linter.unusedSectionVars false

variable {Z : Type*} [NormedAddCommGroup Z] [MeasurableSpace Z]

lemma lipNorm_smul (c : ℝ) (hc : 0 ≤ c) (f : Z → ℝ) :
    WassFSG.Conc.lipNorm (c • f) = c * WassFSG.Conc.lipNorm f := by
  unfold WassFSG.Conc.lipNorm
  rw [Real.mul_iSup_of_nonneg hc]
  refine iSup_congr (fun z => ?_)
  rw [Real.mul_iSup_of_nonneg hc]
  refine iSup_congr (fun z' => ?_)
  rw [Real.mul_iSup_of_nonneg hc]
  refine iSup_congr (fun _ => ?_)
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [← mul_sub, abs_mul, abs_of_nonneg hc, mul_div_assoc]

lemma extIntegral_mono {X : Type*} [MeasurableSpace X] (ν : Measure X) (φ ψ : X → EReal)
    (h : ∀ x, φ x ≤ ψ x) :
    ModelRiskOT.Duality.extIntegral ν φ ≤ ModelRiskOT.Duality.extIntegral ν ψ := by
  unfold ModelRiskOT.Duality.extIntegral
  refine EReal.sub_le_sub ?_ ?_
  · exact EReal.coe_ennreal_le_coe_ennreal_iff.2
      (lintegral_mono (fun x => EReal.toENNReal_le_toENNReal (h x)))
  · exact EReal.coe_ennreal_le_coe_ennreal_iff.2
      (lintegral_mono (fun x => EReal.toENNReal_le_toENNReal (EReal.neg_le_neg_iff.2 (h x))))

lemma expectedRad_mono (P : Measure Z) (n : ℕ) (G G' : Set (Z → ℝ)) (hG : G ⊆ G') :
    WassFSG.Lip.expectedRad P n G ≤ WassFSG.Lip.expectedRad P n G' := by
  unfold WassFSG.Lip.expectedRad
  refine extIntegral_mono _ _ _ (fun z => ?_)
  unfold WassFSG.Lip.radComp
  refine mul_le_mul_of_nonneg_left ?_ (by exact_mod_cast (by positivity : (0:ℝ) ≤ 1 / 2 ^ n))
  refine Finset.sum_le_sum (fun σ _ => ?_)
  exact biSup_mono (fun g hg => hG hg)

end WassFSGT2Aux

open WassFSGT2Aux in
theorem solution {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z] [CompleteSpace Z]
    [MeasurableSpace Z] [BorelSpace Z] [SecondCountableTopology Z]
    (Ptrue : Measure Z) [IsProbabilityMeasure Ptrue] (τ : ℝ) (hT : WassFSG.Lip.IsT1 τ Ptrue)
    (F : Set (Z → ℝ)) (γ₁ : ℝ) (hF : WassFSG.Lip.LipBound γ₁ F) (n : ℕ) (hn : 0 < n)
    (ψ : ℝ → ℝ) (h5 : WassFSG.Lip.SubRootLocalComplexity Ptrue n F ψ)
    (rstar : ℝ) (hrstar : 0 < rstar) (hfix : ψ rstar = rstar) (t : ℝ) (ht : 0 < t) :
    (Measure.pi fun _ : Fin n => Ptrue)
        {z | ∃ f ∈ F, ¬ (∫ x, f x ∂Ptrue ≤ WassFSG.Lip.empMean z f
          + (2 * Real.sqrt (τ * t / n) + Real.sqrt (4 * rstar + 2 / n)) * WassFSG.Conc.lipNorm f
          + 4 * rstar + 2 / n)}
      ≤ ENNReal.ofReal ((WassFSG.Lip.peelCount γ₁ τ t n : ℝ) * Real.exp (-t)) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  set r0 := 4 * rstar + 2 / (n : ℝ) with hr0
  have hr0pos : 0 < r0 := by positivity
  set s := Real.sqrt r0 with hs
  have hspos : 0 < s := Real.sqrt_pos.2 hr0pos
  have hss : s * s = r0 := Real.mul_self_sqrt hr0pos.le
  -- the weight `c(f) = √r₀ / (√r₀ ∨ ‖f‖_Lip)`
  let cf : (Z → ℝ) → ℝ := fun f => s / max s (WassFSG.Conc.lipNorm f)
  have hcpos : ∀ f, 0 < cf f := fun f => div_pos hspos (lt_of_lt_of_le hspos (le_max_left _ _))
  have hcle : ∀ f, cf f ≤ 1 := fun f =>
    (div_le_one (lt_of_lt_of_le hspos (le_max_left _ _))).2 (le_max_left _ _)
  have hLnn : ∀ f : Z → ℝ, 0 ≤ WassFSG.Conc.lipNorm f := by
    intro f
    unfold WassFSG.Conc.lipNorm
    exact Real.iSup_nonneg (fun z => Real.iSup_nonneg (fun z' => Real.iSup_nonneg
      (fun _ => by positivity)))
  have hcL : ∀ f, cf f * WassFSG.Conc.lipNorm f ≤ s := by
    intro f
    have hm : 0 < max s (WassFSG.Conc.lipNorm f) := lt_of_lt_of_le hspos (le_max_left _ _)
    change s / max s (WassFSG.Conc.lipNorm f) * WassFSG.Conc.lipNorm f ≤ s
    rw [div_mul_eq_mul_div, div_le_iff₀ hm]
    exact mul_le_mul_of_nonneg_left (le_max_right _ _) hspos.le
  set Fr : Set (Z → ℝ) := {g | ∃ f ∈ F, g = cf f • f} with hFr
  -- `F_r` satisfies Assumption 1(I) with the same constant
  have hFr1 : WassFSG.Lip.LipBound γ₁ Fr := by
    refine ⟨hF.1, ?_⟩
    rintro g ⟨f, hf, rfl⟩ z z'
    simp only [Pi.smul_apply, smul_eq_mul]
    have h1 := hF.2 f hf z z'
    have h2 : 0 ≤ γ₁ * ‖z' - z‖ := mul_nonneg hF.1.le (norm_nonneg _)
    have := hcpos f
    have := hcle f
    nlinarith
  -- `F_r ⊆` the localized class at level `r₀`
  have hloc : Fr ⊆ WassFSG.Lip.localized F r0 := by
    rintro g ⟨f, hf, rfl⟩
    refine ⟨f, hf, cf f, (hcpos f).le, hcle f, rfl, ?_⟩
    rw [lipNorm_smul _ (hcpos f).le, ← hss]
    have := hcL f
    have := mul_nonneg (hcpos f).le (hLnn f)
    nlinarith
  -- sub-root bound `ψ(r₀) ≤ √(r₀ r⋆)`, so `2ψ(r₀) + 1/n ≤ r₀`
  have hψ : 2 * ψ r0 + 1 / n ≤ r0 := by
    have hr0ge : rstar ≤ r0 := by have : 0 < 2 / (n : ℝ) := by positivity
                                  linarith
    have hanti := h5.1.2.2.1 (Set.mem_Ioi.2 hrstar) (Set.mem_Ioi.2 hr0pos) hr0ge
    simp only at hanti
    rw [hfix] at hanti
    have hsr : 0 < Real.sqrt rstar := Real.sqrt_pos.2 hrstar
    have hsrsq : Real.sqrt rstar * Real.sqrt rstar = rstar := Real.mul_self_sqrt hrstar.le
    rw [div_le_div_iff₀ hspos hsr] at hanti
    -- ψ r0 * √r⋆ ≤ r⋆ * s, i.e. ψ r0 ≤ √r⋆ s
    have hψle : ψ r0 ≤ Real.sqrt rstar * s := by
      have : ψ r0 * Real.sqrt rstar ≤ (Real.sqrt rstar * s) * Real.sqrt rstar := by
        calc ψ r0 * Real.sqrt rstar ≤ rstar * s := hanti
          _ = (Real.sqrt rstar * s) * Real.sqrt rstar := by linear_combination (-s) * hsrsq
      exact le_of_mul_le_mul_right this hsr
    -- (2 √r⋆ s + 1/n ≤ s²) since (s² - 1/n)² - 4 r⋆ s² = 1/n² ≥ 0 ... direct:
    have key : 2 * (Real.sqrt rstar * s) + 1 / n ≤ r0 := by
      have hA : 0 ≤ (2 * Real.sqrt rstar - s) ^ 2 := sq_nonneg _
      have hsq : s * s = 4 * (Real.sqrt rstar * Real.sqrt rstar) + 2 / n := by rw [hss, hsrsq]
      have : (1 : ℝ) / n = (s * s - 4 * (Real.sqrt rstar * Real.sqrt rstar)) / 2 := by
        rw [hsq]; ring
      rw [this, ← hss]
      nlinarith
    linarith
  have hER : WassFSG.Lip.expectedRad Ptrue n Fr ≤ (ψ r0 : EReal) :=
    le_trans (expectedRad_mono _ _ _ _ hloc) (h5.2 r0 hr0pos)
  refine le_trans (measure_mono ?_) (WassFSG.Lip.lemma_12 Ptrue τ hT Fr γ₁ hFr1 t ht n hn)
  intro z hz
  obtain ⟨f, hf, hbad⟩ := hz
  refine ⟨cf f • f, ⟨f, hf, rfl⟩, fun hgood => hbad ?_⟩
  set c := cf f with hc
  have hc0 := hcpos f
  set L := WassFSG.Conc.lipNorm f with hL
  set A := Real.sqrt (τ * t / n) with hA
  have hA0 : 0 ≤ A := Real.sqrt_nonneg _
  rw [lipNorm_smul _ hc0.le] at hgood
  have hint : ∫ x, (c • f) x ∂Ptrue = c * ∫ x, f x ∂Ptrue := by
    simp only [Pi.smul_apply, smul_eq_mul]; exact integral_const_mul c _
  have hemp : WassFSG.Lip.empMean z (c • f) = c * WassFSG.Lip.empMean z f := by
    unfold WassFSG.Lip.empMean
    simp only [Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum]; ring
  rw [hint, hemp] at hgood
  -- turn the extended-real inequality into a real one
  have hreal : c * ∫ x, f x ∂Ptrue ≤ c * WassFSG.Lip.empMean z f + 2 * A * (c * L)
      + 2 * ψ r0 + 1 / n := by
    have h2 : (2 : EReal) * WassFSG.Lip.expectedRad Ptrue n Fr ≤ ((2 * ψ r0 : ℝ) : EReal) := by
      rw [EReal.coe_mul]
      exact mul_le_mul_of_nonneg_left hER (by norm_num)
    have := le_trans hgood (add_le_add (add_le_add le_rfl h2) le_rfl)
    rw [← EReal.coe_add, ← EReal.coe_add, EReal.coe_le_coe_iff] at this
    linarith
  have hreal2 : c * ∫ x, f x ∂Ptrue ≤ c * (WassFSG.Lip.empMean z f + 2 * A * L) + r0 := by
    nlinarith
  have hL0 : 0 ≤ L := hLnn f
  have hsL : 0 ≤ s * L := mul_nonneg hspos.le hL0
  -- `r₀ / c ≤ √r₀ L + r₀` in both cases
  have hdiv : r0 ≤ c * (s * L + r0) := by
    by_cases hcase : L ≤ s
    · have : c = 1 := by
        rw [hc]; change s / max s L = 1; rw [max_eq_left hcase, div_self hspos.ne']
      rw [this]; linarith
    · push Not at hcase
      have : c = s / L := by rw [hc]; change s / max s L = s / L; rw [max_eq_right hcase.le]
      rw [this]
      have hLpos : 0 < L := lt_trans hspos hcase
      rw [div_mul_eq_mul_div, le_div_iff₀ hLpos]
      have : 0 ≤ s * r0 := by positivity
      nlinarith
  have : c * ∫ x, f x ∂Ptrue ≤ c * (WassFSG.Lip.empMean z f + (2 * A + s) * L + r0) := by
    nlinarith
  have := le_of_mul_le_mul_left this hc0
  rw [hr0] at this
  linarith
