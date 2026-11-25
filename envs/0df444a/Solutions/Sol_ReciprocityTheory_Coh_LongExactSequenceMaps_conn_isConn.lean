-- Prove2me | solution 1 for ReciprocityTheory.Coh.LongExactSequenceMaps.conn_isConn
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T14:00:53.734808+00:00
-- url     : https://prove2.me/submissions/1f0fe1ae-be0f-4987-9331-0e893662ed34

import Definitions.Def_ReciprocityTheory_GroupCohomology_CupConnRightStatement
import Definitions.Def_ReciprocityTheory_GroupCohomology_DEqZeroOfMemB
import Definitions.Def_ReciprocityTheory_GroupCohomology_ConnNatHolds
import Theorems.Thm_ReciprocityTheory_Coh_LongExactSequenceMaps_conn_pS

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
noncomputable section
variable {R : Type u} [CommRing R] {A B C : Cx R} (i : Hom A B) (p : Hom B C)
namespace ReciprocityTheory.Coh.LongExactSequenceMaps
theorem _root_.solution (hs : SES i p) : IsConn i p (conn i p hs) := by
  intro n b a hc ha hba
  have hbS : b ∈ S i n := LinearMap.mem_range.2 ⟨a, hba.symm⟩
  exact (conn_pS i p hs n ⟨b, hbS⟩).trans (θ_apply i p hs n ⟨b, hbS⟩ a ha hba)
end ReciprocityTheory.Coh.LongExactSequenceMaps
