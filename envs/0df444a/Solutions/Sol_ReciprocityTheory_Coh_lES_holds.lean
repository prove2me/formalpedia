-- Prove2me | solution 1 for ReciprocityTheory.Coh.lES_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T14:38:38.204847+00:00
-- url     : https://prove2.me/submissions/d392692d-54b2-4f37-aa8c-0ae33fd13249

import Definitions.Def_ReciprocityTheory_GroupCohomology_CupConnRightStatement
import Definitions.Def_ReciprocityTheory_GroupCohomology_DEqZeroOfMemB
import Definitions.Def_ReciprocityTheory_GroupCohomology_ConnNatHolds
import Theorems.Thm_ReciprocityTheory_Coh_LongExactSequenceMaps_conn_isConn
import Theorems.Thm_ReciprocityTheory_Coh_LongExactSequenceMaps_uniq
import Theorems.Thm_ReciprocityTheory_Coh_LongExactSequenceMaps_les_of

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
namespace ReciprocityTheory.Coh
theorem _root_.solution : LESStatement.{u} := by
  intro R _ A B C i p hs
  exact ⟨⟨LongExactSequenceMaps.conn i p hs, LongExactSequenceMaps.conn_isConn i p hs,
    LongExactSequenceMaps.les_of i p hs _ (LongExactSequenceMaps.conn_isConn i p hs)⟩,
    fun δ δ' h h' => LongExactSequenceMaps.uniq i p hs δ δ' h h'⟩
end ReciprocityTheory.Coh
