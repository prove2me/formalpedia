-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.GelfConv.isMulRightInvariant_of_compact
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:48:01.819805+00:00
-- url     : https://prove2.me/submissions/bc3bc026-1e02-4cbd-903c-a5baa2930227

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandPairConvolution_Unimod
import Theorems.Thm_PI_UnitaryGroupMassFormula_GelfConv_eq_of_isMulLeftInvariant_of_univ

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
theorem _root_.solution (μ : Measure G) [μ.IsHaarMeasure] :
    μ.IsMulRightInvariant :=
  ⟨fun g => eq_of_isMulLeftInvariant_of_univ μ (map (· * g) μ)
    (by rw [map_apply (measurable_mul_const g) MeasurableSet.univ, Set.preimage_univ])⟩
end PI.UnitaryGroupMassFormula.GelfConv
