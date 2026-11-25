-- Prove2me | solution 1 for ReciprocityTheory.Coh.KernelCokernelKilling.shC_acyc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T15:00:38.722457+00:00
-- url     : https://prove2.me/submissions/1ded802d-223b-4185-a7e6-834490d1786f

import Definitions.Def_ReciprocityTheory_GroupCohomology_DEqZeroOfMemB
import Definitions.Def_ReciprocityTheory_GroupCohomology_ConnNatHolds
import Definitions.Def_ReciprocityTheory_GroupCohomology_PairHomFCoeOfId
import Definitions.Def_ReciprocityTheory_GroupCohomology_Shapiro
import Definitions.Def_ReciprocityTheory_GroupCohomology_ShiftA
import Theorems.Thm_ReciprocityTheory_Coh_KernelCokernelKilling_triv_H_sub
import Theorems.Thm_ReciprocityTheory_Coh_coindEv_isCoind
import Theorems.Thm_ReciprocityTheory_Coh_shapiro_holds


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
theorem _root_.solution (k : ℕ) (hk : 1 ≤ k) : Subsingleton ((shC M).H k) := by
  have hq := shapiro_holds R G (⊥ : Subgroup G) (M.resSub ⊥) (shC M) (coindEv _ _)
    (coindEv_isCoind _ _) ⟨fun _ => 1, continuous_const, fun x g => Subsingleton.elim _ _⟩
  have := triv_H_sub (M.resSub (⊥ : Subgroup G)) k hk
  exact (hq k).1.subsingleton
end ReciprocityTheory.Coh.KernelCokernelKilling
