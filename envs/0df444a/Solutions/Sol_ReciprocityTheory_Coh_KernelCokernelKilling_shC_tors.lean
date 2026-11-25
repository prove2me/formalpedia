-- Prove2me | solution 1 for ReciprocityTheory.Coh.KernelCokernelKilling.shC_tors
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T13:55:04.016212+00:00
-- url     : https://prove2.me/submissions/34de9536-71c4-4660-990d-58f857c7995a

import Definitions.Def_ReciprocityTheory_GroupCohomology_DEqZeroOfMemB
import Definitions.Def_ReciprocityTheory_GroupCohomology_ConnNatHolds
import Definitions.Def_ReciprocityTheory_GroupCohomology_PairHomFCoeOfId
import Definitions.Def_ReciprocityTheory_GroupCohomology_Shapiro
import Definitions.Def_ReciprocityTheory_GroupCohomology_ShiftA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.Coh
open ReciprocityTheory.Gal Cx Function
noncomputable section
universe u
open ReciprocityTheory.Coh.KernelCokernelKilling
variable {R : Type u} [CommRing R] {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] (M : TRep R G) [DiscreteTopology M.V]
namespace ReciprocityTheory.Coh.KernelCokernelKilling
theorem _root_.solution (hM : ∀ m : M.V, ∃ k : ℕ, 0 < k ∧ k • m = 0) :
    ∀ f : (shC M).V, ∃ k : ℕ, 0 < k ∧ k • f = 0 := by
  intro f
  choose k hk using hM
  have hfin : (Set.range f.1).Finite := (isCompact_range f.1.continuous).finite_of_discrete
  obtain ⟨s, hs⟩ : ∃ s : Finset M.V, ∀ g, f.1 g ∈ s :=
    ⟨hfin.toFinset, fun g => hfin.mem_toFinset.2 ⟨g, rfl⟩⟩
  refine ⟨∏ m ∈ s, k m, Finset.prod_pos fun m _ => (hk m).1, ?_⟩
  have key : ∀ v ∈ s, (∏ m ∈ s, k m) • v = 0 := by
    intro v hv
    obtain ⟨d, hd⟩ := Finset.dvd_prod_of_mem k hv
    rw [hd, mul_comm, mul_smul, (hk v).2, smul_zero]
  exact Subtype.ext (ContinuousMap.ext fun g => key _ (hs g))
end ReciprocityTheory.Coh.KernelCokernelKilling
