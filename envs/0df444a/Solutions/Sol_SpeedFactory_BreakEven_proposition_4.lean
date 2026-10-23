-- Prove2me | solution 1 for SpeedFactory.BreakEven.proposition_4
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-22T07:08:11.202779+00:00
-- url     : https://prove2.me/submissions/e46fc15a-a65b-419e-9007-e4edd74245fa

import Mathlib
import Definitions.Def_SpeedFactory_BreakEven_Model
import Definitions.Def_SpeedFactory_BreakEven_Dynamics
import Theorems.Thm_SpeedFactory_BreakEven_eq_19

open MeasureTheory ProbabilityTheory
open SpeedFactory.BreakEven

theorem solution (M : Model) (hM : M.Standing) {α : ℝ} (hα : α ∈ Set.Ioo (-1 : ℝ) 1)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (d : ℕ → Ω → ℝ) (hd : IIDNormalDemand M P d)
    (i0 j0 : ℝ) (pipe0 : Fin (M.L - 1) → ℝ) :
    (Cond21 M α →
      ConcaveOn ℝ (Set.Ioc (0 : ℝ) 1) (pMinus M α) ∧
      ∀ γ ∈ Set.Ioc (0 : ℝ) 1, pMinus M α γ < M.p → M.p < M.u →
        costTBS M γ α i0 P d < costOUT M j0 pipe0 P d) ∧
    (¬ Cond21 M α →
      ConvexOn ℝ (Set.Ioc (0 : ℝ) 1) (pMinus M α) ∧
      ∀ γ ∈ Set.Ioc (0 : ℝ) 1, pMinus M α γ < M.p →
        (∀ γ' ∈ Set.Ico (0 : ℝ) 1, costTBS M 1 α i0 P d < costTBS M γ' α i0 P d) ∧
        costTBS M 1 α i0 P d < costOUT M j0 pipe0 P d) := by
  have h19 := SpeedFactory.BreakEven.eq_19 M hM hα P d hd i0 j0 pipe0
  obtain ⟨hμ, hσ, hh, hb, hu, hm, -, -⟩ := hM
  obtain ⟨K, hK⟩ : ∃ K : ℝ, K = (M.h + M.b) * (sigmaI M α - sigmaIS M) * stdNormalPDF (zi M)
      + M.u * M.m * sigmaQ M α * stdNormalPDF (zq M) := ⟨_, rfl⟩
  have hpm : ∀ γ, pMinus M α γ = K / M.μ * γ⁻¹ + M.u := by
    intro γ; simp only [pMinus, hK]; ring
  have hdiff : ∀ γ ∈ Set.Icc (0 : ℝ) 1,
      costTBS M γ α i0 P d - costOUT M j0 pipe0 P d = K + M.μ * γ * (M.u - M.p) := by
    intro γ hγ; rw [h19 γ hγ, hK]
  have hσq : 0 < sigmaQ M α := by
    obtain ⟨h1, h2⟩ := hα
    unfold sigmaQ
    apply mul_pos hσ
    apply Real.sqrt_pos.mpr
    apply div_pos <;> linarith
  have hφq : 0 < stdNormalPDF (zq M) := gaussianPDFReal_pos _ _ _ one_ne_zero
  have hcond : Cond21 M α ↔ K < 0 := by
    have hD : 0 < M.u * M.m * sigmaQ M α * stdNormalPDF (zq M) := by
      have : 0 < M.m := by linarith
      positivity
    have heq : (M.h + M.b) / (M.u * M.m) * ((sigmaIS M - sigmaI M α) / sigmaQ M α)
        * (stdNormalPDF (zi M) / stdNormalPDF (zq M))
        = ((M.h + M.b) * (sigmaIS M - sigmaI M α) * stdNormalPDF (zi M))
          / (M.u * M.m * sigmaQ M α * stdNormalPDF (zq M)) := by
      have : 0 < M.m := by linarith
      field_simp
    unfold Cond21
    rw [heq, one_lt_div hD, hK]
    constructor <;> intro h <;> linarith
  have hinv : ConvexOn ℝ (Set.Ioc (0 : ℝ) 1) fun x : ℝ => x⁻¹ := by
    have := (convexOn_zpow (𝕜 := ℝ) (-1)).subset Set.Ioc_subset_Ioi_self (convex_Ioc 0 1)
    simpa using this
  refine ⟨fun hc => ?_, fun hc => ?_⟩
  · have hK0 : K < 0 := hcond.mp hc
    refine ⟨?_, ?_⟩
    · have hc' : 0 ≤ -(K / M.μ) := by
        have : K / M.μ < 0 := div_neg_of_neg_of_pos hK0 hμ
        linarith
      have h1 := (hinv.smul hc').neg.add (concaveOn_const (c := M.u) (convex_Ioc 0 1))
      have hf : pMinus M α = fun x => -((-(K / M.μ)) • x⁻¹) + M.u := by
        funext x; rw [hpm x, smul_eq_mul]; ring
      rw [hf]; exact h1
    · intro γ hγ hp _
      have hγ0 := hγ.1
      have := hdiff γ ⟨hγ.1.le, hγ.2⟩
      rw [hpm γ] at hp
      have hKe : K = (K / M.μ * γ⁻¹) * (M.μ * γ) := by field_simp
      have : (K / M.μ * γ⁻¹) * (M.μ * γ) < (M.p - M.u) * (M.μ * γ) := by
        apply mul_lt_mul_of_pos_right (by linarith) (by positivity)
      nlinarith
  · have hK0 : 0 ≤ K := by
      by_contra h; exact hc (hcond.mpr (lt_of_not_ge h))
    refine ⟨?_, ?_⟩
    · have hc' : 0 ≤ K / M.μ := div_nonneg hK0 hμ.le
      have h1 := (hinv.smul hc').add (convexOn_const (c := M.u) (convex_Ioc 0 1))
      have hf : pMinus M α = fun x => (K / M.μ) • x⁻¹ + M.u := by
        funext x; rw [hpm x, smul_eq_mul]
      rw [hf]; exact h1
    · intro γ hγ hp
      have hγ0 := hγ.1
      rw [hpm γ] at hp
      have hKμ : 0 ≤ K / M.μ := div_nonneg hK0 hμ.le
      have hge : K / M.μ ≤ K / M.μ * γ⁻¹ := by
        have : 1 ≤ γ⁻¹ := one_le_inv₀ hγ0 |>.mpr hγ.2
        nlinarith
      have hup : M.u < M.p := by
        have : 0 ≤ K / M.μ * γ⁻¹ := mul_nonneg hKμ (inv_nonneg.mpr hγ0.le)
        linarith
      have h1 := hdiff 1 ⟨zero_le_one, le_refl _⟩
      refine ⟨?_, ?_⟩
      · intro γ' hγ'
        have h2 := hdiff γ' ⟨hγ'.1, hγ'.2.le⟩
        have : M.μ * 1 * (M.u - M.p) < M.μ * γ' * (M.u - M.p) := by
          have h3 : 0 < M.μ * (1 - γ') * (M.p - M.u) := by
            have := hγ'.2
            apply mul_pos (mul_pos hμ (by linarith)) (by linarith)
          nlinarith
        linarith
      · have hKe : K = (K / M.μ) * M.μ := by field_simp
        have : K / M.μ < M.p - M.u := by linarith
        have : K < (M.p - M.u) * M.μ := by
          rw [hKe]; exact mul_lt_mul_of_pos_right this hμ
        nlinarith
