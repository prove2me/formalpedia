-- Prove2me | solution 1 for PI.VolStabW.us_exists_open
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:57:33.189792+00:00
-- url     : https://prove2.me/submissions/28fb9eaf-7f2b-447a-ae7c-6ede2933bead

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_VolStabFromSWW
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_Unimod
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_InvInvSt
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_UnimodStab

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolStabW
open MeasureTheory Measure Topology Set Function
open scoped Pointwise ENNReal NNReal
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [T2Space G] [MeasurableSpace G] [BorelSpace G]
namespace PI.VolStabW
theorem _root_.solution (μ : Measure G) [IsHaarMeasure μ] :
    ∃ U : Set G, IsOpen U ∧ (1 : G) ∈ U ∧ U⁻¹ = U ∧ 0 < μ U ∧ μ U < ⊤ := by
  obtain ⟨V, hVc, hV1⟩ := exists_compact_mem_nhds (1 : G)
  set U := interior V ∩ (interior V)⁻¹ with hUdef
  have h1 : (1 : G) ∈ U := ⟨mem_interior_iff_mem_nhds.2 hV1,
    by rw [Set.mem_inv, inv_one]; exact mem_interior_iff_mem_nhds.2 hV1⟩
  have hUo : IsOpen U := isOpen_interior.inter isOpen_interior.inv
  refine ⟨U, hUo, h1, ?_, hUo.measure_pos μ ⟨1, h1⟩, ?_⟩
  · rw [hUdef, Set.inter_inv, inv_inv, inter_comm]
  · exact lt_of_le_of_lt (measure_mono (inter_subset_left.trans interior_subset))
      hVc.measure_lt_top
end PI.VolStabW
