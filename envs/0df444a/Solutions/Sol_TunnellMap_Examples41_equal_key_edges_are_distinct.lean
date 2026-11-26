-- Prove2me | solution 1 for TunnellMap.Examples41.equal_key_edges_are_distinct
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T17:39:05.696721+00:00
-- url     : https://prove2.me/submissions/8ae1ef98-348f-491d-b11d-550a84fcb458

import Definitions.Def_TunnellMap_Examples41
import Definitions.Def_TunnellMap_Examples41Residual
import Theorems.Thm_TunnellMap_Examples41_signed_orbit_edge_key
import Theorems.Thm_TunnellMap_Examples41_edgeKey_s3_t4

set_option autoImplicit true
open TunnellMap
open TunnellMap.Examples41
set_option maxRecDepth 10000
namespace TunnellMap.Examples41
theorem _root_.solution :
    representativeEdgeKey s1 t1 = representativeEdgeKey s3 t4 ∧
      s1 ≠ s3 ∧ t1 ≠ t4 := by
  constructor
  · rw [signed_orbit_edge_key, edgeKey_s3_t4]
    rfl
  · constructor <;> intro h
    · have := congrArg (fun s : BResidual 41 => s.1.1.y) h
      norm_num [s1, s3] at this
    · have := congrArg (fun t : AResidual 41 => t.1.1.z) h
      norm_num [t1, t4] at this
end TunnellMap.Examples41
