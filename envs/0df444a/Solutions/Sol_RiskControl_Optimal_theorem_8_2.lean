-- Prove2me | solution 2 for RiskControl.Optimal.theorem_8
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-27T09:48:19.14406+00:00
-- url     : https://prove2.me/submissions/b0352ce9-e6ab-4b81-aa1d-862961d58fdd

import Mathlib
import Definitions.Def_RiskControl_Optimal_Setting
import Theorems.Thm_RiskControl_Optimal_setdiff_condLoss_ge
import Theorems.Thm_RiskControl_Optimal_setdiff_size_ge

-- carved verbatim out of submission a9e62213-7e9c-4495-a24f-f3660a1c1b79, lines 253-266

section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
open RiskControl.Optimal

lemma rco_exp {𝒳 𝒴 𝒵 : Type*} [MeasurableSpace 𝒳] [MeasurableSpace 𝒴]
    [MeasurableSpace 𝒵]
    (P : Measure (𝒳 × 𝒴)) (μ : Measure 𝒵) [IsFiniteMeasure μ]
    (A B : 𝒳 → Set 𝒵) (hA : MeasurableSet {q : 𝒳 × 𝒵 | q.2 ∈ A q.1})
    (hB : MeasurableSet {q : 𝒳 × 𝒵 | q.2 ∈ B q.1})
    (h : ∫⁻ x, μ (A x \ B x) ∂P.fst ≤ ∫⁻ x, μ (B x \ A x) ∂P.fst) :
    expSize P μ A ≤ expSize P μ B := by
  unfold expSize
  have hAx : ∀ x, MeasurableSet (A x) := fun x => measurable_prodMk_left hA
  have hBx : ∀ x, MeasurableSet (B x) := fun x => measurable_prodMk_left hB
  have hmeas : ∀ (C D : 𝒳 → Set 𝒵), MeasurableSet {q : 𝒳 × 𝒵 | q.2 ∈ C q.1} →
      MeasurableSet {q : 𝒳 × 𝒵 | q.2 ∈ D q.1} → Measurable (fun x => μ (C x ∩ D x)) := by
    intro C D hC hD
    have := hC.inter hD
    exact measurable_measure_prodMk_left (ν := μ) this
  have hdiff : ∀ (C D : 𝒳 → Set 𝒵), MeasurableSet {q : 𝒳 × 𝒵 | q.2 ∈ C q.1} →
      MeasurableSet {q : 𝒳 × 𝒵 | q.2 ∈ D q.1} → Measurable (fun x => μ (C x \ D x)) := by
    intro C D hC hD
    have := hC.inter hD.compl
    exact measurable_measure_prodMk_left (ν := μ) this
  have e1 : ∀ x, μ (A x) = μ (A x \ B x) + μ (A x ∩ B x) := fun x =>
    (measure_diff_add_inter (A x) (hBx x)).symm
  have e2 : ∀ x, μ (B x) = μ (B x \ A x) + μ (A x ∩ B x) := fun x => by
    rw [Set.inter_comm]; exact (measure_diff_add_inter (B x) (hAx x)).symm
  simp_rw [e1, e2]
  rw [lintegral_add_left (hdiff A B hA hB), lintegral_add_left (hdiff B A hB hA)]
  exact add_le_add h le_rfl

lemma rco_graph {𝒳 𝒴 𝒵 : Type*} [MeasurableSpace 𝒳] [MeasurableSpace 𝒴]
    [MeasurableSpace 𝒵]
    (ℓ : 𝒴 → 𝒵 → ℝ≥0) (hℓ : Measurable (Function.uncurry ℓ))
    (κ : Kernel 𝒳 𝒴) [IsMarkovKernel κ] (lam : ℝ) :
    MeasurableSet {q : 𝒳 × 𝒵 | q.2 ∈ thresholdSet κ ℓ lam q.1} := by
  have hmc : Measurable (fun q : 𝒳 × 𝒵 => condLoss κ ℓ q.1 q.2) := by
    have hf : Measurable (Function.uncurry (fun (q : 𝒳 × 𝒵) (y : 𝒴) => (ℓ y q.2 : ℝ≥0∞))) :=
      measurable_coe_nnreal_ennreal.comp
        (hℓ.comp (f := fun p : (𝒳 × 𝒵) × 𝒴 => (p.2, p.1.2))
          (measurable_snd.prodMk (measurable_snd.comp measurable_fst)))
    have := Measurable.lintegral_kernel_prod_right
      (κ := Kernel.comap κ Prod.fst measurable_fst) hf
    simpa [condLoss, Kernel.comap_apply] using this
  exact measurableSet_le measurable_const hmc

theorem solution {𝒳 𝒴 𝒵 : Type*} [MeasurableSpace 𝒳] [MeasurableSpace 𝒴]
    [MeasurableSpace 𝒵]
    (P : Measure (𝒳 × 𝒴)) [IsProbabilityMeasure P]
    (μ : Measure 𝒵) [IsFiniteMeasure μ]
    (ℓ : 𝒴 → 𝒵 → ℝ≥0) (hℓ : Measurable (Function.uncurry ℓ))
    (κ : Kernel 𝒳 𝒴) [IsMarkovKernel κ] (hκ : P.fst ⊗ₘ κ = P)
    (lam : ℝ) (hlam : lam < 0)
    (T' : 𝒳 → Set 𝒵) (hT' : MeasurableSet {q : 𝒳 × 𝒵 | q.2 ∈ T' q.1})
    (hR : risk P μ ℓ T' ≤ risk P μ ℓ (thresholdSet κ ℓ lam)) :
    expSize P μ (thresholdSet κ ℓ lam) ≤ expSize P μ T' := by
  have h1 := RiskControl.Optimal.setdiff_condLoss_ge P μ ℓ hℓ κ hκ lam hlam T' hT' hR
  have h2 := RiskControl.Optimal.setdiff_size_ge P μ ℓ hℓ κ lam hlam T' hT' h1
  exact rco_exp P μ (thresholdSet κ ℓ lam) T' (rco_graph ℓ hℓ κ lam) hT' h2

end
