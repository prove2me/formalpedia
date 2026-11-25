-- Prove2me | solution 1 for P2M_GroundTheory_GroupCoh_split__surjective_ddf379839ca5
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T08:19:13.210935+00:00
-- url     : https://prove2.me/submissions/b131287e-793c-43d7-aa32-2d5e4edb5403

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_SplittingModule
import Definitions.Def_GroundTheory_TateCohomology_CohTrivial
import Definitions.Def_GroundTheory_TateCohomology_ResCores
import Definitions.Def_GroundTheory_TateCohomology_SplittingCohTrivial
import Theorems.Thm_P2M_GroundTheory_GroupCoh_split__augClass_80c011573ab3

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open CategoryTheory Limits groupCohomology Rep
open GroundTheory GroundTheory.GroupCoh
universe u
variable {G : Type} [Group G] [Fintype G] (M : Rep ℤ G) (u : groupCohomology M 2)
variable (S : Subgroup G) [Fintype S]
omit [Fintype S]
namespace GroundTheory.GroupCoh
theorem _root_.solution
    (h3 : ∀ y : groupCohomology (res S.subtype M) 2, ∃ m : ℤ, y = m • resClass M u S) :
    Function.Surjective (splitδ M u S) := by
  intro y
  obtain ⟨m, rfl⟩ := h3 y
  exact ⟨m • augClass S, by rw [map_zsmul, splitδ_augClass]⟩
end GroundTheory.GroupCoh
