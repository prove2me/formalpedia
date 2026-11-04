-- Prove2me | solution 1 for ThreeSum.TernaryTypeCardinality.encode_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:00:54.522939+00:00
-- url     : https://prove2.me/submissions/06a1dbc2-1d0e-455a-8da0-da47662243be

import Definitions.Def_Submission_ThreeSum_TernaryCoverLocal
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Sigma
import Definitions.Def_Submission_ThreeSum_TernaryTypeCardinality
import Theorems.Thm_ThreeSum_TernaryTypeCardinality_decode_encode
import Theorems.Thm_ThreeSum_HashFamily_hashMap_apply
attribute [local simp] ThreeSum.HashFamily.hashMap_apply



set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryTypeCardinality
open Finset ThreeSum.TernaryJointType ThreeSum.TernaryCoverLocal
set_option maxHeartbeats 2000000
namespace ThreeSum.TernaryTypeCardinality
theorem _root_.solution (L : ℕ) : Function.Injective (@encode L) := by
  intro w v h
  have hh := congrArg decode h
  simpa [decode_encode] using hh
end ThreeSum.TernaryTypeCardinality
