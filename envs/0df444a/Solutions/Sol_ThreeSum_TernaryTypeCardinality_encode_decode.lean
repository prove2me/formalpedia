-- Prove2me | solution 1 for ThreeSum.TernaryTypeCardinality.encode_decode
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:56:57.622499+00:00
-- url     : https://prove2.me/submissions/9eb2553d-d135-445e-895f-3cb603722f9f

import Definitions.Def_Submission_ThreeSum_TernaryCoverLocal
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Sigma
import Definitions.Def_Submission_ThreeSum_TernaryTypeCardinality
import Theorems.Thm_ThreeSum_TernaryTypeCardinality_positions_decode_two
import Theorems.Thm_ThreeSum_TernaryTypeCardinality_positions_decode_one
import Theorems.Thm_ThreeSum_HashFamily_hashMap_apply
attribute [local simp] ThreeSum.HashFamily.hashMap_apply



set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryTypeCardinality
open Finset ThreeSum.TernaryJointType ThreeSum.TernaryCoverLocal
set_option maxHeartbeats 2000000
namespace ThreeSum.TernaryTypeCardinality
theorem _root_.solution {L : ℕ} (p : Pair L) (hd : Disjoint p.1 p.2) :
    encode (decode p)=p := by
  cases p with
  | mk t o =>
    have h2 := positions_decode_two (⟨t,o⟩ : Pair L)
    have h1 := positions_decode_one (⟨t,o⟩ : Pair L) hd
    simp only [encode,h2,h1]
end ThreeSum.TernaryTypeCardinality
