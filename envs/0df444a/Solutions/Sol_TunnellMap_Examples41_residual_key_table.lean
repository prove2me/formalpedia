-- Prove2me | solution 1 for TunnellMap.Examples41.residual_key_table
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T17:11:43.840605+00:00
-- url     : https://prove2.me/submissions/19ee3f93-7e59-435d-9a7e-d966216c4232

import Definitions.Def_TunnellMap_Examples41
import Definitions.Def_TunnellMap_Examples41Residual
import Theorems.Thm_TunnellMap_Examples41_signed_orbit_edge_key
import Theorems.Thm_TunnellMap_Examples41_edgeKey_s1_t2
import Theorems.Thm_TunnellMap_Examples41_edgeKey_s1_t3
import Theorems.Thm_TunnellMap_Examples41_edgeKey_s1_t4
import Theorems.Thm_TunnellMap_Examples41_edgeKey_s2_t1
import Theorems.Thm_TunnellMap_Examples41_edgeKey_s2_t2
import Theorems.Thm_TunnellMap_Examples41_edgeKey_s2_t3
import Theorems.Thm_TunnellMap_Examples41_edgeKey_s2_t4
import Theorems.Thm_TunnellMap_Examples41_edgeKey_s3_t1
import Theorems.Thm_TunnellMap_Examples41_edgeKey_s3_t2
import Theorems.Thm_TunnellMap_Examples41_edgeKey_s3_t3
import Theorems.Thm_TunnellMap_Examples41_edgeKey_s3_t4
import Theorems.Thm_TunnellMap_Examples41_edgeKey_s4_t1
import Theorems.Thm_TunnellMap_Examples41_edgeKey_s4_t2
import Theorems.Thm_TunnellMap_Examples41_edgeKey_s4_t3
import Theorems.Thm_TunnellMap_Examples41_edgeKey_s4_t4

set_option autoImplicit true
open TunnellMap
open TunnellMap.Examples41
set_option maxRecDepth 10000
namespace TunnellMap.Examples41
theorem _root_.solution :
    representativeEdgeKey s1 t1 = key41 5 1 (-1) (-1) ∧
      representativeEdgeKey s1 t3 = key41 5 1 1 (-1) ∧
      representativeEdgeKey s1 t2 = key41 20 1 (-4) (-1) ∧
      representativeEdgeKey s1 t4 = key41 20 1 4 (-1) ∧
      representativeEdgeKey s2 t1 = key41 5 1 (-1) 1 ∧
      representativeEdgeKey s2 t4 = key41 5 1 1 1 ∧
      representativeEdgeKey s2 t2 = key41 20 1 (-4) 1 ∧
      representativeEdgeKey s2 t3 = key41 20 1 4 1 ∧
      representativeEdgeKey s3 t4 = key41 5 1 (-1) (-1) ∧
      representativeEdgeKey s3 t2 = key41 5 1 1 (-1) ∧
      representativeEdgeKey s3 t3 = key41 20 1 (-4) (-1) ∧
      representativeEdgeKey s3 t1 = key41 20 1 4 (-1) ∧
      representativeEdgeKey s4 t3 = key41 5 1 (-1) 1 ∧
      representativeEdgeKey s4 t2 = key41 5 1 1 1 ∧
      representativeEdgeKey s4 t4 = key41 20 1 (-4) 1 ∧
      representativeEdgeKey s4 t1 = key41 20 1 4 1 := by
  exact ⟨signed_orbit_edge_key, edgeKey_s1_t3, edgeKey_s1_t2, edgeKey_s1_t4,
    edgeKey_s2_t1, edgeKey_s2_t4, edgeKey_s2_t2, edgeKey_s2_t3,
    edgeKey_s3_t4, edgeKey_s3_t2, edgeKey_s3_t3, edgeKey_s3_t1,
    edgeKey_s4_t3, edgeKey_s4_t2, edgeKey_s4_t4, edgeKey_s4_t1⟩
end TunnellMap.Examples41
