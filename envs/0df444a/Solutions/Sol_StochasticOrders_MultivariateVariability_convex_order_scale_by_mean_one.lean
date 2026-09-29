-- Prove2me | solution 1 for StochasticOrders.MultivariateVariability.convex_order_scale_by_mean_one
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-25T05:29:05.596628+00:00
-- url     : https://prove2.me/submissions/91d3d71f-7403-4a92-a58e-dc1a3f135516

import Mathlib
import Definitions.Def_StochasticOrders_MultivariateVariability_ConvexOrder

set_option autoImplicit false

open MeasureTheory ProbabilityTheory StochasticOrders.MultivariateVariability in
theorem solution {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → Fin n → ℝ) (U : Ω → ℝ)
    (hX : Measurable X) (hU : Measurable U) (hIndep : IndepFun X U μ)
    (hUnn : 0 ≤ᵐ[μ] U) (hUmean : ∫ ω, U ω ∂μ = 1) :
    ConvexOrder μ μ X (fun ω => U ω • X ω) := by
  intro φ hconv hφX hφY
  have hφc : Continuous φ := continuousOn_univ.1 (hconv.continuousOn isOpen_univ)
  have hUint : Integrable U μ := by
    by_contra h
    rw [integral_undef h] at hUmean
    exact zero_ne_one hUmean
  set PX : Measure (Fin n → ℝ) := μ.map X with hPX
  set PU : Measure ℝ := μ.map U with hPU
  have : IsProbabilityMeasure PX := Measure.isProbabilityMeasure_map hX.aemeasurable
  have : IsProbabilityMeasure PU := Measure.isProbabilityMeasure_map hU.aemeasurable
  have hjoint : μ.map (fun ω => (X ω, U ω)) = PX.prod PU :=
    (indepFun_iff_map_prod_eq_prod_map_map hX.aemeasurable hU.aemeasurable).1 hIndep
  set F : (Fin n → ℝ) × ℝ → ℝ := fun p => φ (p.2 • p.1) with hF
  have hFc : Continuous F := hφc.comp (continuous_snd.smul continuous_fst)
  have hXU : Measurable (fun ω => (X ω, U ω)) := hX.prodMk hU
  have hFint : Integrable F (PX.prod PU) := by
    rw [← hjoint]
    exact (integrable_map_measure hFc.aestronglyMeasurable hXU.aemeasurable).2 hφY
  have hRHS : ∫ ω, φ (U ω • X ω) ∂μ = ∫ x, ∫ u, F (x, u) ∂PU ∂PX := by
    rw [← integral_prod F hFint, ← hjoint,
      integral_map hXU.aemeasurable hFc.aestronglyMeasurable]
  have hLHS : ∫ ω, φ (X ω) ∂μ = ∫ x, φ x ∂PX := by
    rw [hPX, integral_map hX.aemeasurable hφc.aestronglyMeasurable]
  have hidint : Integrable (fun u : ℝ => u) PU :=
    (integrable_map_measure aestronglyMeasurable_id hU.aemeasurable).2 hUint
  have hmeanU : ∫ u, u ∂PU = 1 := by
    rw [hPU, integral_map (f := fun u : ℝ => u) hU.aemeasurable aestronglyMeasurable_id]
    exact hUmean
  rw [hRHS, hLHS]
  refine integral_mono_ae ((integrable_map_measure hφc.aestronglyMeasurable
    hX.aemeasurable).2 hφX) hFint.integral_prod_left ?_
  filter_upwards [hFint.prod_right_ae] with x hx
  have hJ := hconv.map_integral_le (μ := PU) (f := fun u : ℝ => u • x) hφc.continuousOn
    isClosed_univ (Filter.Eventually.of_forall fun _ => Set.mem_univ _)
    (hidint.smul_const x) hx
  rw [integral_smul_const, hmeanU, one_smul] at hJ
  exact hJ
