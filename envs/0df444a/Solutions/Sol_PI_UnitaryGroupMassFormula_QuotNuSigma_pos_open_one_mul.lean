-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.QuotNuSigma.pos_open_one_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:50:47.520374+00:00
-- url     : https://prove2.me/submissions/564143c8-fdc2-4a3f-a356-4beb794be4eb

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_QuotNuSigma
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuotientSigmaFiniteness_SigmaFiniteOfWeil
import Theorems.Thm_PI_UnitaryGroupMassFormula_QuotNuSigma_pos_open_one

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped ENNReal Pointwise
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.QuotNuSigma
variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
namespace PI.UnitaryGroupMassFormula.QuotNuSigma
theorem _root_.solution (A B : Set G) (μA μB : Measure G) [SigmaFinite μB]
    (hA0 : μA ≠ 0) (hAc : μA Aᶜ = 0) (hAi : ∀ s ∈ A, μA.map (fun x => s * x) = μA)
    (hB0 : μB ≠ 0) (hBc : μB Bᶜ = 0) (hBi : ∀ s ∈ B, μB.map (fun x => s * x) = μB)
    (U : Set G) (hU : IsOpen U) (h1 : (1 : G) ∈ U) :
    0 < ((μA.prod μB).map (fun p : G × G => p.1 * p.2)) U := by
  obtain ⟨V, hVo, hV1, hVV⟩ := exists_open_nhds_one_mul_subset (hU.mem_nhds h1)
  have hApos := pos_open_one A μA hA0 hAc hAi V hVo hV1
  have hBpos := pos_open_one B μB hB0 hBc hBi V hVo hV1
  have hsub : V ×ˢ V ⊆ (fun p : G × G => p.1 * p.2) ⁻¹' U := fun p hp =>
    hVV (Set.mul_mem_mul hp.1 hp.2)
  calc (0 : ℝ≥0∞) < μA V * μB V := ENNReal.mul_pos hApos.ne' hBpos.ne'
    _ = (μA.prod μB) (V ×ˢ V) := (Measure.prod_prod V V).symm
    _ ≤ (μA.prod μB) ((fun p : G × G => p.1 * p.2) ⁻¹' U) := measure_mono hsub
    _ ≤ _ := Measure.le_map_apply measurable_mul.aemeasurable U
end PI.UnitaryGroupMassFormula.QuotNuSigma
