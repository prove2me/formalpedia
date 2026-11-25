-- Prove2me | solution 1 for PI.LocHaarRRW.exists_haar_of_subgroup
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T09:50:57.646278+00:00
-- url     : https://prove2.me/submissions/99e19e9b-4c67-4928-aaf3-b8799f29b43e

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalHaarSubgroup_ExistsHaarOfSubgroup

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ValuativeRel MeasureTheory Topology Polynomial
open PI PI.LocHaarRRW
variable {V : Type*} [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V]
  [MeasurableSpace V] [BorelSpace V]
namespace PI.LocHaarRRW
theorem _root_.solution [SigmaCompactSpace V] (R : AddSubgroup V)
    (h0 : (R : Set V) ∈ 𝓝 (0 : V)) {C : Set V} (hC : IsCompact C) (hRC : (R : Set V) ⊆ C) :
    ∃ μ : Measure V, μ.IsAddHaarMeasure ∧ SigmaFinite μ ∧ μ (R : Set V) = 1 := by
  have hRo : IsOpen (R : Set V) := AddSubgroup.isOpen_of_mem_nhds R h0
  have hRc : IsClosed (R : Set V) := R.isClosed_of_isOpen hRo
  have hRk : IsCompact (R : Set V) := hC.of_isClosed_subset hRc hRC
  let K0 : TopologicalSpace.PositiveCompacts V :=
    { carrier := R, isCompact' := hRk,
      interior_nonempty' := by rw [hRo.interior_eq]; exact ⟨0, R.zero_mem⟩ }
  refine ⟨Measure.addHaarMeasure K0, inferInstance, inferInstance, ?_⟩
  exact Measure.addHaarMeasure_self
end PI.LocHaarRRW
