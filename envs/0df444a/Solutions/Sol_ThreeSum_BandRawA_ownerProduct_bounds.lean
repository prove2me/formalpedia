-- Prove2me | solution 1 for ThreeSum.BandRawA.ownerProduct_bounds
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:37:25.669116+00:00
-- url     : https://prove2.me/submissions/59225af7-da4b-430e-9a4e-9b04d6f19fa7

import Definitions.Def_Submission_ThreeSum_BandRawAScore
import Definitions.Def_Submission_ThreeSum_BandRawAFinite
import Theorems.Thm_ThreeSum_BandRawA_bandPositions_lt
import Theorems.Thm_ThreeSum_BandRawA_mem_ownerProduct


set_option autoImplicit false
open ThreeSum ThreeSum.BandRawA
open BandCandidateRows Finset
open scoped BigOperators
set_option maxHeartbeats 2000000
set_option maxRecDepth 8000
namespace ThreeSum.BandRawA
theorem _root_.solution {nA nB nC g s : ℕ} {rs : List Record} {t : ℕ × ℕ × ℕ}
    (hs : s < rs.length) (ht : t ∈ ownerProduct nA nB nC g rs s) :
    t.1 < (items nA g rs).length ∧ t.2.1 < nB ∧ t.2.2 < nC := by
  obtain ⟨ha,_,hb,hc⟩ := (mem_ownerProduct hs).mp ht
  exact ⟨ha,bandPositions_lt hb,bandPositions_lt hc⟩
end ThreeSum.BandRawA
