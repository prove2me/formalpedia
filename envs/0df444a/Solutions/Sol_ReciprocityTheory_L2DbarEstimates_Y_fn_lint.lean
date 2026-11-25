-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.Y.fn_lint
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T16:22:29.054865+00:00
-- url     : https://prove2.me/submissions/22e98e82-c998-4d4a-860f-c52886e90e56

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_FlatNullA
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_FlatNullB
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_fn_symm_aemeas
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_fn_rho_aemeas
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_fn_map

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y
open MeasureTheory Filter Topology WeightedAtlas Set
open scoped ContDiff ENNReal
noncomputable section
universe u
variable {n : ℕ} {Y : Type u} [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y]
  [MeasurableSpace Y] [BorelSpace Y] {ι : Type*} {La : Type*} [AddCommGroup La]
  (A : WeightedAtlas n Y ι La) {L : La} {N : ℕ} {w : Fin N → ι → Y → ℂ} {w0 : ι → Y → ℂ}
  {s : Fin n → ι → Y → ℂ} {De : MvPolynomial (Fin n) ℂ}
namespace ReciprocityTheory.L2DbarEstimates.Y
theorem _root_.solution (i : ι) {φ : Y → ℝ≥0∞} (hφ : Measurable φ) :
    ∫⁻ x in (A.chart i).source, φ x ∂A.mu =
      ∫⁻ v in (A.chart i).target, fnRho A i v * φ ((A.chart i).symm v) := by
  have hsymm : AEMeasurable (A.chart i).symm
      ((volume.restrict (A.chart i).target).withDensity (fnRho A i)) :=
    (fn_symm_aemeas A i).mono_ac (withDensity_absolutelyContinuous _ _)
  rw [← fn_map A i, lintegral_map' hφ.aemeasurable hsymm]
  exact lintegral_withDensity_eq_lintegral_mul₀ (fn_rho_aemeas A i)
    (hφ.comp_aemeasurable (fn_symm_aemeas A i))
end ReciprocityTheory.L2DbarEstimates.Y
