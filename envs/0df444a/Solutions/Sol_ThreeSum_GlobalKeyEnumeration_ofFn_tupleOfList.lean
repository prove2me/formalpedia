-- Prove2me | solution 1 for ThreeSum.GlobalKeyEnumeration.ofFn_tupleOfList
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:11:58.884197+00:00
-- url     : https://prove2.me/submissions/af8d59fb-3536-4bf6-b9db-57925a1ac0e9

import Definitions.Def_Submission_ThreeSum_RadixKeyLists
import Definitions.Def_Submission_ThreeSum_LocalMaskGraph
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.ProdSigma
import Definitions.Def_Submission_ThreeSum_GlobalKeyEnumeration

set_option autoImplicit false
open ThreeSum ThreeSum.GlobalKeyEnumeration
open GlobalEncoding LocalGraph LocalCoverBounds LocalHashMoments
open RadixKeyLists
open scoped BigOperators
set_option maxHeartbeats 1800000
namespace ThreeSum.GlobalKeyEnumeration
theorem _root_.solution {α : Type*} {J : ℕ} (xs : List α) (hlen : xs.length=J) :
    List.ofFn (tupleOfList xs hlen)=xs := by
  subst J
  exact List.ofFn_get xs
end ThreeSum.GlobalKeyEnumeration
