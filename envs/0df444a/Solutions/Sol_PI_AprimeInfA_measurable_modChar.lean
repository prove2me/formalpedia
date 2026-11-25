-- Prove2me | solution 1 for PI.AprimeInfA.measurable_modChar
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T09:18:55.093998+00:00
-- url     : https://prove2.me/submissions/a8082373-8a42-4792-84b3-edfa82bbefc2

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ArchimedeanOrbitMeasures_LintegralMulRightOfMem
import Theorems.Thm_PI_AprimeInfA_map_mul_right_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.AprimeInfA
open MeasureTheory Topology TopologicalSpace Set
open scoped ENNReal NNReal
variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [T2Space G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
namespace PI.AprimeInfA
theorem _root_.solution :
    Measurable (fun g : G => (Measure.modularCharacterFun g : ℝ≥0∞)) := by

  obtain ⟨K, hK, hK1⟩ := exists_compact_mem_nhds (1 : G)
  set μ : Measure G := Measure.haar
  have hpos : μ K ≠ 0 := by
    first
    | exact (Measure.measure_pos_of_mem_nhds μ hK1).ne'
    | exact (MeasureTheory.measure_pos_of_mem_nhds μ hK1).ne'
    | exact ((isOpen_interior.measure_pos μ ⟨1, mem_interior_iff_mem_nhds.2 hK1⟩).trans_le
        (measure_mono interior_subset)).ne'
  have hfin : μ K ≠ ∞ := hK.measure_lt_top.ne
  have key : (fun g : G => (Measure.modularCharacterFun g : ℝ≥0∞)) =
      fun g => (∫⁻ x, K.indicator 1 (x * g) ∂μ) / μ K := by
    funext g
    have e := congrArg (fun m : Measure G => m K) (map_mul_right_eq μ g)
    simp only [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul] at e
    rw [Measure.map_apply (measurable_mul_const g) hK.measurableSet] at e
    rw [ENNReal.eq_div_iff hpos hfin, mul_comm, ← e,
      ← lintegral_indicator_one (hK.measurableSet.preimage (measurable_mul_const g))]
    rfl
  rw [key]
  refine Measurable.div_const ?_ _
  exact ((measurable_one.indicator hK.measurableSet).comp
    (measurable_snd.mul measurable_fst)).lintegral_prod_right'
end PI.AprimeInfA
