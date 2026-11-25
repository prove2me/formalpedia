-- Prove2me | solution 1 for ReciprocityTheory.Coh.CCA.res_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T13:46:14.252638+00:00
-- url     : https://prove2.me/submissions/e36e13fb-36ad-4535-8d40-5cded92e35ae

import Definitions.Def_ReciprocityTheory_GroupCohomology_CupCorA
import Definitions.Def_ReciprocityTheory_GroupCohomology_CupCorB

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.Coh ReciprocityTheory.Coh.CCA
open ReciprocityTheory.Gal Cx Function
noncomputable section
universe u
variable {R : Type u} [CommRing R]
variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (U : Subgroup G)
namespace ReciprocityTheory.Coh.CCA
theorem _root_.solution {N : TRep R G} (n : ℕ) (F : (Fin (n + 1) → G) → N.V) (hF : F ∈ hcoch N G n) :
    F ∈ hcoch (N.resSub U) G n := by
  simp only [hcoch] at hF ⊢
  exact ⟨hF.1, fun g x => hF.2 g x⟩
end ReciprocityTheory.Coh.CCA
