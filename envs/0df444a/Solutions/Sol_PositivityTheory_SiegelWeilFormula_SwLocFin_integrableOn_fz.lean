-- Prove2me | solution 1 for PositivityTheory.SiegelWeilFormula.SwLocFin.integrableOn_fz
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:59:03.054774+00:00
-- url     : https://prove2.me/submissions/ad055e20-ffdb-4fb6-a67e-ad3833f563d9

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_SiegelWeilFormula_LocalCharacterIntegrals_DifferentiableSetIntegralFz
import Theorems.Thm_PositivityTheory_SiegelWeilFormula_SwLocFin_norm_cpow_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PositivityTheory PositivityTheory.SiegelWeilFormula PositivityTheory.SiegelWeilFormula.SwLocFin
open MeasureTheory Filter Topology Set
variable {H : Type*} [MeasurableSpace H]
namespace PositivityTheory.SiegelWeilFormula.SwLocFin
theorem _root_.solution {ν : Measure H} {r : H → ℝ} {u : H → ℂ} {s₀ : ℂ} (hr1 : ∀ b, 1 ≤ r b) (hrm : Measurable r)
    (hum : AEStronglyMeasurable u ν) {C : ℝ} (hub : ∀ b, ‖u b‖ ≤ C) {S : Set H} (hS : MeasurableSet S)
    (hSf : ν S < ⊤) {Rm : ℝ} (hRm : ∀ b ∈ S, r b ≤ Rm) (z : ℂ) : IntegrableOn (fz r u s₀ z) S ν := by
  have hmeas : Measurable fun b => (r b : ℂ) ^ (-(z - s₀)) :=
    (Complex.measurable_ofReal.comp hrm).pow_const _
  refine Measure.integrableOn_of_bounded (M := Rm ^ max (-(z - s₀)).re 0 * C) hSf.ne
    (hmeas.aestronglyMeasurable.mul hum) ?_
  filter_upwards [ae_restrict_mem hS] with b hb
  show ‖(r b : ℂ) ^ (-(z - s₀)) * u b‖ ≤ Rm ^ max (-(z - s₀)).re 0 * C
  rw [norm_mul]
  exact mul_le_mul (PositivityTheory.SiegelWeilFormula.SwLocFin.norm_cpow_le (hr1 b) (hRm b hb) _) (hub b)
    (norm_nonneg _) (Real.rpow_nonneg (by linarith [hr1 b, hRm b hb]) _)
end PositivityTheory.SiegelWeilFormula.SwLocFin
