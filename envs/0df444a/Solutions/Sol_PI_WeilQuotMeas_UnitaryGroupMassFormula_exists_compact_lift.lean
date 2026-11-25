-- Prove2me | solution 1 for PI.WeilQuotMeas.UnitaryGroupMassFormula.exists_compact_lift
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T11:12:07.059945+00:00
-- url     : https://prove2.me/submissions/166cd478-410f-4644-a6bf-38bea4f93635

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_WeilQuotMeas
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilQuotientMeasure_StepBruhat
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilQuotientMeasure_LintegralMulAvgComm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Topology
open scoped ENNReal Pointwise
open PI PI.WeilQuotMeas PI.WeilQuotMeas.UnitaryGroupMassFormula
variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [T2Space G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] {H : Subgroup G}
namespace PI.WeilQuotMeas.UnitaryGroupMassFormula
theorem _root_.solution (K : Set (G ⧸ H)) (hK : IsCompact K) :
    ∃ C : Set G, IsCompact C ∧ K ⊆ (QuotientGroup.mk : G → G ⧸ H) '' C := by
  have hopen : IsOpenMap (QuotientGroup.mk : G → G ⧸ H) := QuotientGroup.isOpenMap_coe
  choose V hVc hxV using fun x : G => exists_compact_mem_nhds x
  have hcov : K ⊆ ⋃ x : G, (QuotientGroup.mk : G → G ⧸ H) '' interior (V x) := by
    intro y _
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
    exact Set.mem_iUnion.2 ⟨x, x, mem_interior_iff_mem_nhds.2 (hxV x), rfl⟩
  obtain ⟨s, hs⟩ := hK.elim_finite_subcover _ (fun x => hopen _ isOpen_interior) hcov
  refine ⟨⋃ x ∈ s, V x, s.isCompact_biUnion fun x _ => hVc x, hs.trans ?_⟩
  simp only [Set.iUnion_subset_iff]
  intro x hx
  refine Set.image_mono (interior_subset.trans ?_)
  intro z hz
  exact Set.mem_iUnion₂.2 ⟨x, hx, hz⟩
end PI.WeilQuotMeas.UnitaryGroupMassFormula
