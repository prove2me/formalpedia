-- Prove2me | solution 1 for ReciprocityTheory.Coh.FiniteLevelCohomology.exists_nhds_right_const
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T13:45:21.213297+00:00
-- url     : https://prove2.me/submissions/c4df4aa5-e9f9-47ba-a450-fda0a29bd059

import Definitions.Def_ReciprocityTheory_GroupCohomology_CupConnRightStatement
import Definitions.Def_ReciprocityTheory_GroupCohomology_DEqZeroOfMemB
import Definitions.Def_ReciprocityTheory_GroupCohomology_ResNormalHolds
import Definitions.Def_ReciprocityTheory_GroupCohomology_InfRes
import Definitions.Def_ReciprocityTheory_GroupCohomology_FiniteLevel

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.Coh
open ReciprocityTheory.Gal Topology
open scoped Pointwise
universe u
open ReciprocityTheory.Coh.FiniteLevelCohomology
namespace ReciprocityTheory.Coh.FiniteLevelCohomology
theorem _root_.solution {K X : Type*} [Group K] [TopologicalSpace K] [IsTopologicalGroup K]
    [CompactSpace K] [TopologicalSpace X] [DiscreteTopology X] (f : K → X) (hf : Continuous f) :
    ∃ V ∈ 𝓝 (1 : K), ∀ g v, v ∈ V → f (g * v) = f g := by
  have hfin : (Set.range f).Finite := (isCompact_range hf).finite_of_discrete
  have hV : ∀ x ∈ Set.range f, ∃ V ∈ 𝓝 (1 : K), f ⁻¹' {x} * V ⊆ f ⁻¹' {x} := by
    intro x _
    have hc : IsClosed (f ⁻¹' {x}) := (isClosed_discrete {x}).preimage hf
    exact compact_open_separated_mul_right hc.isCompact ((isOpen_discrete {x}).preimage hf) subset_rfl
  choose! V hV1 hV2 using hV
  refine ⟨⋂ x ∈ hfin.toFinset, V x, ?_, ?_⟩
  · exact (Filter.biInter_finset_mem _).2 fun x hx => hV1 x (hfin.mem_toFinset.1 hx)
  · intro g v hv
    have hx : f g ∈ Set.range f := ⟨g, rfl⟩
    have hvx : v ∈ V (f g) := Set.mem_iInter₂.1 hv (f g) (hfin.mem_toFinset.2 hx)
    exact hV2 (f g) hx (Set.mul_mem_mul (show f g ∈ ({f g} : Set X) from rfl) hvx)
end ReciprocityTheory.Coh.FiniteLevelCohomology
