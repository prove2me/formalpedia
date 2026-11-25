-- Prove2me | solution 1 for PI.NMeasInv.UnitaryGroupMassFormula.haarOn_unique
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:09:30.378444+00:00
-- url     : https://prove2.me/submissions/1a85d94a-0679-4df0-b13d-eebd30cf17a7

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MeasureInverseContraction_RightInvOfContract
import Theorems.Thm_PI_NMeasInv_UnitaryGroupMassFormula_haarOn_props
import Theorems.Thm_PI_NMeasInv_UnitaryGroupMassFormula_haar_unique

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
theorem _root_.solution (N : Subgroup G) (hN : IsClosed (N : Set G)) {μ ν : Measure G} (hμ : HaarOn N μ)
    (hν : HaarOn N ν) : ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ⊤ ∧ ν = c • μ := by
  have hfμ : IsFiniteMeasureOnCompacts μ := ⟨fun K hK => (haarOn_props N hN μ hμ).1 K hK⟩
  have hfν : IsFiniteMeasureOnCompacts ν := ⟨fun K hK => (haarOn_props N hN ν hν).1 K hK⟩
  obtain ⟨c, hct, hc⟩ :=
    haar_unique N hN μ ν hμ.2.1 hμ.2.2.1 hμ.2.2.2 hfμ hν.2.2.1 hν.2.2.2 hfν
  refine ⟨c, ?_, hct, hc⟩
  rintro rfl
  apply hν.2.1
  rw [hc, zero_smul]
end PI.NMeasInv.UnitaryGroupMassFormula
