-- Prove2me | solution 1 for ThreeSum.BandRawA.ownerProduct_disjoint
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:37:03.960247+00:00
-- url     : https://prove2.me/submissions/0793f5f9-e58c-4cfb-beb1-f9e5695c5e8b

import Definitions.Def_Submission_ThreeSum_BandRawAIndex
import Definitions.Def_Submission_ThreeSum_BandWeightedScore
import Definitions.Def_Submission_ThreeSum_BandRawAProduct
import Theorems.Thm_ThreeSum_BandRawA_mem_ownerProduct

set_option autoImplicit false
open ThreeSum ThreeSum.BandRawA
open BandCandidateRows Finset
open scoped BigOperators
set_option maxHeartbeats 1900000
set_option maxRecDepth 8000
namespace ThreeSum.BandRawA
theorem _root_.solution {nA nB nC g s t : ℕ} {rs : List Record}
    (hs : s < rs.length) (ht : t < rs.length) (hst : s ≠ t) :
    Disjoint (ownerProduct nA nB nC g rs s) (ownerProduct nA nB nC g rs t) := by
  apply disjoint_left.mpr
  intro x hx hy
  have hs' := (mem_ownerProduct hs).mp hx
  have ht' := (mem_ownerProduct ht).mp hy
  exact hst (hs'.2.1.symm.trans ht'.2.1)
end ThreeSum.BandRawA
