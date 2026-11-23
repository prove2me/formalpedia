-- Prove2me | solution 1 for PI.AprimeInfA.avg_mul_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:14:05.029801+00:00
-- url     : https://prove2.me/submissions/ef197fa5-22e9-41ab-95b6-1dc4dfeabce9

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ArchimedeanOrbitMeasures_LintegralMulRightOfMem

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
theorem _root_.solution (H : Subgroup G) (ν : Measure H) [ν.IsMulLeftInvariant] (f : G → ℝ≥0∞)
    (g : G) (k : H) : ∫⁻ h, f (g * k * (h : G)) ∂ν = ∫⁻ h, f (g * (h : G)) ∂ν := by

  haveI : MeasurableMul H := by
    first
    | infer_instance
    | exact ⟨fun c => ((measurable_const_mul (c : G)).comp measurable_subtype_coe).subtype_mk,
        fun c => ((measurable_mul_const (c : G)).comp measurable_subtype_coe).subtype_mk⟩
  have e := lintegral_mul_left_eq_self (μ := ν) (fun h : H => f (g * (h : G))) k
  simpa [mul_assoc] using e
end PI.AprimeInfA
