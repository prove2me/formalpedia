-- Prove2me | solution 1 for PI.VolStabW.DiscreteGroups.cover
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:53:24.8928+00:00
-- url     : https://prove2.me/submissions/4a4b527b-7bef-4222-b3e8-74ef045a8bae

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_FibGlue
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_FibDis

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolStabW PI.VolStabW.DiscreteGroups
open MeasureTheory Topology Set Filter PI.VolStabW PI.VolStabW.Glue
open scoped ENNReal
variable {V : Type} [TopologicalSpace V] [T2Space V] [LocallyCompactSpace V]
  [SecondCountableTopology V]
namespace PI.VolStabW.DiscreteGroups
theorem _root_.solution (U : Set V) (hU : IsOpen U) : ∃ W : ℕ → Set V,
    (∀ n, IsOpen (W n) ∧ IsCompact (closure (W n)) ∧ closure (W n) ⊆ U) ∧ ⋃ n, W n = U := by
  haveI : LocallyCompactSpace U := hU.isOpenEmbedding_subtypeVal.locallyCompactSpace
  let E := CompactExhaustion.choice U
  have h : ∀ n, ∃ W, IsOpen W ∧ Subtype.val '' E n ⊆ W ∧ closure W ⊆ U ∧ IsCompact (closure W) :=
    fun n => exists_open_between_and_isCompact_closure ((E.isCompact n).image continuous_subtype_val)
      hU (by rintro _ ⟨u, -, rfl⟩; exact u.2)
  choose W hW1 hW2 hW3 hW4 using h
  refine ⟨W, fun n => ⟨hW1 n, hW4 n, hW3 n⟩,
    subset_antisymm (iUnion_subset fun n => subset_closure.trans (hW3 n)) ?_⟩
  intro x hx
  obtain ⟨n, hn⟩ := E.exists_mem ⟨x, hx⟩
  exact mem_iUnion.2 ⟨n, hW2 n ⟨_, hn, rfl⟩⟩
end PI.VolStabW.DiscreteGroups
