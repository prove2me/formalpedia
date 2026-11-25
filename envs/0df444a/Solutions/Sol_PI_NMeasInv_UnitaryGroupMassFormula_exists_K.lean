-- Prove2me | solution 1 for PI.NMeasInv.UnitaryGroupMassFormula.exists_K
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T07:02:58.929087+00:00
-- url     : https://prove2.me/submissions/5e08842c-9ace-40de-b844-c0102dca1919

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MeasureInverseContraction_RightInvOfContract
import Theorems.Thm_PI_NMeasInv_UnitaryGroupMassFormula_haarOn_props

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
theorem _root_.solution (N : Subgroup G) (hN : IsClosed (N : Set G)) (μ : Measure G) (hμ : HaarOn N μ) :
    ∃ K : Set G, IsCompact K ∧ 0 < μ K ∧ μ K < ⊤ := by
  obtain ⟨hfin, hpos⟩ := haarOn_props N hN μ hμ
  obtain ⟨K, hK, hK1⟩ := exists_compact_mem_nhds (1 : G)
  refine ⟨K, hK, ?_, hfin K hK⟩
  have h1 : (1 : G) ∈ interior K := mem_interior_iff_mem_nhds.mpr hK1
  exact lt_of_lt_of_le (hpos _ isOpen_interior ⟨1, h1, N.one_mem⟩) (measure_mono interior_subset)
end PI.NMeasInv.UnitaryGroupMassFormula
