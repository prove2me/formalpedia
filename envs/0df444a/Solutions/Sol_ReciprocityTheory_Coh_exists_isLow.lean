-- Prove2me | solution 1 for ReciprocityTheory.Coh.exists_isLow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T14:17:59.754563+00:00
-- url     : https://prove2.me/submissions/67d1bc0d-9f5f-4683-8f61-4bdd4a03d4ed

import Definitions.Def_ReciprocityTheory_GroupCohomology_TransgressionStatement
import Definitions.Def_ReciprocityTheory_GroupCohomology_LowHolds
import Definitions.Def_ReciprocityTheory_GroupCohomology_IsLowExists
import Theorems.Thm_ReciprocityTheory_Coh_low_holds


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.Coh
universe u
namespace ReciprocityTheory.Coh
theorem _root_.solution {R : Type u} [CommRing R] {G : Type u} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] (M : TRep R G) : ∃ e₀ e₁ e₂, IsLow M e₀ e₁ e₂ := by
  obtain ⟨-, ⟨e₀, h₀⟩, ⟨e₁, h₁⟩, e₂, h₂⟩ := low_holds R G M
  exact ⟨e₀, e₁, e₂, h₀, h₁, h₂⟩
end ReciprocityTheory.Coh
