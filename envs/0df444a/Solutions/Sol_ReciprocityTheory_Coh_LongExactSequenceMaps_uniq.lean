-- Prove2me | solution 1 for ReciprocityTheory.Coh.LongExactSequenceMaps.uniq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T13:48:29.070435+00:00
-- url     : https://prove2.me/submissions/2a2e44cf-db7c-4771-bf36-8cc85f787a46

import Definitions.Def_ReciprocityTheory_GroupCohomology_CupConnRightStatement
import Definitions.Def_ReciprocityTheory_GroupCohomology_DEqZeroOfMemB
import Definitions.Def_ReciprocityTheory_GroupCohomology_ConnNatHolds

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.Coh
open Cx Function
universe u
open ReciprocityTheory.Coh.LongExactSequenceMaps
variable {R : Type u} [CommRing R] {A B C : Cx R} (i : Hom A B) (p : Hom B C)
namespace ReciprocityTheory.Coh.LongExactSequenceMaps
theorem _root_.solution (hs : SES i p) (δ δ' : ∀ n, C.H n →ₗ[R] A.H (n + 1)) (hδ : IsConn i p δ)
    (hδ' : IsConn i p δ') : δ = δ' := by
  funext n
  refine LinearMap.ext fun h => ?_
  obtain ⟨b, a, hc, ha, hba, rfl⟩ := rep i p hs n h
  rw [hδ n b a hc ha hba, hδ' n b a hc ha hba]
end ReciprocityTheory.Coh.LongExactSequenceMaps
