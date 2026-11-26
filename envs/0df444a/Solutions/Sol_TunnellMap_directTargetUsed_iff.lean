-- Prove2me | solution 1 for TunnellMap.directTargetUsed_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:22:51.995162+00:00
-- url     : https://prove2.me/submissions/588f877f-b57c-45f7-9897-9207187be956

import Definitions.Def_TunnellMap_OrbitRanking
import Definitions.Def_TunnellMap_ResidualTargetTest
import Theorems.Thm_TunnellMap_exists_odd_four_mul_iff
import Theorems.Thm_TunnellMap_exists_odd_two_mul_iff

set_option autoImplicit true
open TunnellMap
namespace TunnellMap
theorem _root_.solution {n : ℤ} (p : ARep n) :
    DirectTargetUsed p ↔ ImageUsedTriple p.1 := by
  unfold DirectTargetUsed ImageUsedTriple ImagePredicate1 ImagePredicate2
    ImagePredicate3
  rw [exists_odd_four_mul_iff, exists_odd_four_mul_iff, exists_odd_two_mul_iff]
end TunnellMap
