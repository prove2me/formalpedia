-- Prove2me | solution 1 for PI.NMeasInv.UnitaryGroupMassFormula.smul_cancel
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T06:56:55.64463+00:00
-- url     : https://prove2.me/submissions/1b84688d-7664-48b3-9a4c-700cc850134f

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MeasureInverseContraction_RightInvOfContract

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Measure Topology
open scoped ENNReal NNReal
open PI PI.NMeasInv PI.NMeasInv.UnitaryGroupMassFormula
attribute [local instance] Classical.propDecidable
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
namespace PI.NMeasInv.UnitaryGroupMassFormula
theorem _root_.solution {μ : Measure G} {K : Set G} (hK0 : 0 < μ K) (hKt : μ K < ⊤) {c d : ℝ≥0∞}
    (h : c • μ = d • μ) : c = d := by
  have h' := congrArg (fun ν : Measure G => ν K) h
  simp only [Measure.smul_apply, smul_eq_mul] at h'
  have h'' := congrArg (· / μ K) h'
  simpa [ENNReal.mul_div_cancel_right hK0.ne' hKt.ne] using h''
end PI.NMeasInv.UnitaryGroupMassFormula
