-- Prove2me | solution 1 for ResidualsDRO.Wass.theorem_7_display_3
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-04T11:31:51.321107+00:00
-- url     : https://prove2.me/submissions/5a698e60-6b3c-47a6-b4bb-baf28defc050

import Mathlib
import Definitions.Def_WassersteinDRO_Duality_wassersteinDistance
import Definitions.Def_ResidualsDRO_Wass_Setting
import Definitions.Def_ResidualsDRO_Wass_Radius
import Theorems.Thm_ResidualsDRO_Wass_lemma_3
import Theorems.Thm_ResidualsDRO_Wass_lemma_6
import Theorems.Thm_ResidualsDRO_Wass_theorem_7_display_2

open MeasureTheory ProbabilityTheory

open ResidualsDRO.Wass in
theorem solution {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {dx dy n : ℕ} (hdy : 1 ≤ dy) (hn : 1 ≤ n)
    (p a : ℝ) (hp : 1 ≤ p) (hpdy : p ≠ (dy : ℝ) / 2)
    (𝒴 : Set (EuclideanSpace ℝ (Fin dy)))
    (h𝒴c : IsClosed 𝒴) (h𝒴v : Convex ℝ 𝒴) (h𝒴n : 𝒴.Nonempty)
    (proj : EuclideanSpace ℝ (Fin dy) → EuclideanSpace ℝ (Fin dy))
    (hproj : IsNearestPointProj 𝒴 proj)
    (Pε : Measure (EuclideanSpace ℝ (Fin dy))) [IsProbabilityMeasure Pε]
    (hA1 : Assumption1 Pε p a)
    (fstar : EuclideanSpace ℝ (Fin dx) → EuclideanSpace ℝ (Fin dy))
    (fhat : Ω → EuclideanSpace ℝ (Fin dx) → EuclideanSpace ℝ (Fin dy))
    (xs : Fin n → Ω → EuclideanSpace ℝ (Fin dx))
    (eps : Fin n → Ω → EuclideanSpace ℝ (Fin dy)) (heps_meas : ∀ i, Measurable (eps i))
    (heps_indep : iIndepFun eps P) (heps_law : ∀ i, P.map (eps i) = Pε)
    (x : EuclideanSpace ℝ (Fin dx)) (hY : ∀ i ω, fstar x + eps i ω ∈ 𝒴)
    (κ : ℝ → ℝ) (hA2 : Assumption2 P fstar fhat xs p x κ)
    (c₁ c₂ : ℝ) (hc₁ : 0 < c₁) (hc₂ : 0 < c₂) (hL2 : Lemma2Bound P Pε fstar eps x dy p a c₁ c₂)
    (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1) :
    P {ω | ENNReal.ofReal (radius κ c₁ c₂ a p dy n α) <
        WassersteinDRO.Duality.wassersteinDistance p
          (erEmpirical proj fstar (fhat ω) (fun i => xs i ω) (fun i => eps i ω) x)
          (condLaw Pε fstar x)} ≤
      ENNReal.ofReal α := by
  -- κ^{(1)} > 0
  have hk1 : 0 < kappa1 κ α := by
    unfold kappa1
    have := (hA2 (α / 4) (by linarith) (by linarith)).1
    linarith
  -- κ^{(2)} ≥ 0
  have hk2 : 0 ≤ kappa2 c₁ c₂ a p dy n α := by
    unfold kappa2
    split_ifs with h
    · set b := Real.log (2 * c₁ * α⁻¹) / (c₂ * n)
      set y := min (p / (dy : ℝ)) (1 / 2)
      have hy0 : 0 < y := lt_min (div_pos (by linarith) (by exact_mod_cast hdy)) (by norm_num)
      have hy1 : y ≤ 1 / 2 := min_le_right _ _
      rcases le_or_gt 0 b with hb | hb
      · exact Real.rpow_nonneg hb _
      · rw [Real.rpow_def_of_neg hb]
        apply mul_nonneg (Real.exp_pos _).le
        apply Real.cos_nonneg_of_neg_pi_div_two_le_of_le
        · nlinarith [Real.pi_pos]
        · nlinarith [Real.pi_pos]
    · push Not at h
      have hL : 0 < Real.log (2 * c₁ * α⁻¹) := by
        have : 0 < Real.log (2 * c₁ * α⁻¹) / c₂ :=
          lt_trans (by exact_mod_cast (show (0:ℝ) < n by exact_mod_cast hn)) h
        exact (div_pos_iff_of_pos_right hc₂).1 this
      apply Real.rpow_nonneg
      exact (div_pos hL (mul_pos hc₂ (by exact_mod_cast hn))).le
  set B1 := {ω | 2 * κ (α / 4) <
        powerMean p (fun i => ‖epsTilde fstar (fhat ω) (fun j => xs j ω) (fun j => eps j ω) x i‖)}
  set B2 := {ω | ENNReal.ofReal (kappa2 c₁ c₂ a p dy n α) <
        WassersteinDRO.Duality.wassersteinDistance p (trueEmpirical fstar (fun i => eps i ω) x)
          (condLaw Pε fstar x)}
  have hsub : {ω | ENNReal.ofReal (radius κ c₁ c₂ a p dy n α) <
        WassersteinDRO.Duality.wassersteinDistance p
          (erEmpirical proj fstar (fhat ω) (fun i => xs i ω) (fun i => eps i ω) x)
          (condLaw Pε fstar x)} ⊆ B1 ∪ B2 := by
    intro ω hω
    simp only [Set.mem_setOf_eq] at hω
    by_contra hc
    simp only [Set.mem_union, B1, B2, Set.mem_setOf_eq, not_or, not_lt] at hc
    obtain ⟨h1, h2⟩ := hc
    have h3 := lemma_3 (xs := fun i => xs i ω) (eps := fun i => eps i ω) hn p hp 𝒴 h𝒴c h𝒴v
      h𝒴n proj hproj Pε fstar (fhat ω) x (fun i => hY i ω)
    have : WassersteinDRO.Duality.wassersteinDistance p
          (erEmpirical proj fstar (fhat ω) (fun i => xs i ω) (fun i => eps i ω) x)
          (condLaw Pε fstar x) ≤ ENNReal.ofReal (radius κ c₁ c₂ a p dy n α) := by
      refine h3.trans ?_
      unfold radius
      rw [ENNReal.ofReal_add hk1.le hk2]
      gcongr
      unfold kappa1
      exact h1
    exact absurd hω (not_lt.2 this)
  calc _ ≤ P (B1 ∪ B2) := measure_mono hsub
    _ ≤ P B1 + P B2 := measure_union_le _ _
    _ ≤ ENNReal.ofReal (α / 2) + ENNReal.ofReal (α / 2) := by
        gcongr
        · exact lemma_6 P hn p hp fstar fhat xs eps x κ hA2 α hα0 hα1
        · exact theorem_7_display_2 P hdy hn p a hp hpdy Pε hA1 fstar eps heps_meas heps_indep
            heps_law x c₁ c₂ hc₁ hc₂ hL2 α hα0 hα1
    _ = ENNReal.ofReal α := by
        rw [← ENNReal.ofReal_add (by linarith) (by linarith)]
        congr 1; ring
