-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.GelfConv.isInvInvariant_of_compact
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:53:22.486713+00:00
-- url     : https://prove2.me/submissions/cf5b837f-cf0b-4706-9d8f-728bf55324b6

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandPairConvolution_Unimod
import Theorems.Thm_PI_UnitaryGroupMassFormula_GelfConv_eq_of_isMulLeftInvariant_of_univ
import Theorems.Thm_PI_UnitaryGroupMassFormula_GelfConv_isMulRightInvariant_of_compact

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.GelfConv
open MeasureTheory Measure
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [MeasurableSpace G] [BorelSpace G]
namespace PI.UnitaryGroupMassFormula.GelfConv
theorem _root_.solution (μ : Measure G) [μ.IsHaarMeasure] : μ.IsInvInvariant := by
  have := isMulRightInvariant_of_compact μ
  have : IsFiniteMeasure μ.inv := ⟨by rw [inv_apply, Set.inv_univ]; exact measure_lt_top _ _⟩
  exact ⟨eq_of_isMulLeftInvariant_of_univ μ μ.inv (by rw [inv_apply, Set.inv_univ])⟩
end PI.UnitaryGroupMassFormula.GelfConv
