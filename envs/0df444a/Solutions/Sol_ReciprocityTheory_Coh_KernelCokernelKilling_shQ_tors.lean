-- Prove2me | solution 1 for ReciprocityTheory.Coh.KernelCokernelKilling.shQ_tors
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T14:33:22.612022+00:00
-- url     : https://prove2.me/submissions/8831232a-dae0-4da4-a6ad-d1ec50241114

import Definitions.Def_ReciprocityTheory_GroupCohomology_DEqZeroOfMemB
import Definitions.Def_ReciprocityTheory_GroupCohomology_ConnNatHolds
import Definitions.Def_ReciprocityTheory_GroupCohomology_PairHomFCoeOfId
import Definitions.Def_ReciprocityTheory_GroupCohomology_Shapiro
import Definitions.Def_ReciprocityTheory_GroupCohomology_ShiftA
import Theorems.Thm_ReciprocityTheory_Coh_KernelCokernelKilling_shC_tors

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
    ∀ q : (shQ M).V, ∃ k : ℕ, 0 < k ∧ k • q = 0 := by
  intro q
  induction q using Submodule.Quotient.induction_on with
  | H f =>
    obtain ⟨k, hk, hf⟩ := shC_tors M hM f
    refine ⟨k, hk, ?_⟩
    have := map_nsmul (LinearMap.range (shI M)).mkQ k f
    rw [hf, map_zero] at this
    exact this.symm
end ReciprocityTheory.Coh.KernelCokernelKilling
