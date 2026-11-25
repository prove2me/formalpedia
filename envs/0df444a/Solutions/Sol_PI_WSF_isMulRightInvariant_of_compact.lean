-- Prove2me | solution 1 for PI.WSF.isMulRightInvariant_of_compact
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T11:11:55.622426+00:00
-- url     : https://prove2.me/submissions/a5616668-5957-43cf-a94f-5e774e41c4ff

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SchurOrthogonality_InstMeasurableSpaceMat
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SchurOrthogonality_ConstructionB

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.WSF
open Formalism.BasicNotions MvPolynomial MeasureTheory Measure TopologicalSpace Matrix
namespace PI.WSF
theorem _root_.solution {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [IsHaarMeasure μ] : IsMulRightInvariant μ := by
  constructor
  intro g
  haveI : (Measure.map (fun x => x * g) μ).IsHaarMeasure := Measure.isHaarMeasure_map_mul_right μ g
  have huniv : Measure.map (fun x => x * g) μ Set.univ = μ Set.univ := by
    rw [Measure.map_apply (measurable_mul_const g) MeasurableSet.univ, Set.preimage_univ]
  have hfin : μ Set.univ ≠ ⊤ := measure_ne_top μ _
  have hpos : μ Set.univ ≠ 0 := (isOpen_univ.measure_pos μ Set.univ_nonempty).ne'
  have hc : (Measure.map (fun x => x * g) μ).haarScalarFactor μ = 1 := by
    have h1 := Measure.measure_isHaarMeasure_eq_smul_of_isOpen (Measure.map (fun x => x * g) μ) μ
      isOpen_univ
    rw [huniv, ENNReal.smul_def] at h1
    have h2 : ((((Measure.map (fun x => x * g) μ).haarScalarFactor μ : NNReal) : ENNReal)) = 1 := by
      have h3 : (((Measure.map (fun x => x * g) μ).haarScalarFactor μ : NNReal) : ENNReal) * μ Set.univ =
          1 * μ Set.univ := by
        rw [one_mul]
        exact h1.symm
      exact (ENNReal.mul_left_inj hpos hfin).mp h3
    exact_mod_cast h2
  refine MeasureTheory.ext_of_generate_finite {s : Set G | IsOpen s}
    BorelSpace.measurable_eq isPiSystem_isOpen ?_ huniv
  intro s hs
  rw [Measure.measure_isHaarMeasure_eq_smul_of_isOpen _ μ hs, hc, one_smul]
end PI.WSF
