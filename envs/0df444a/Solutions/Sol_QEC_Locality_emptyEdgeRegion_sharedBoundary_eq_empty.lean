-- Prove2me | solution 1 for QEC.Locality.emptyEdgeRegion_sharedBoundary_eq_empty
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-05T19:25:11.634803+00:00
-- url     : https://prove2.me/submissions/e66bdf91-9f53-4b0a-940b-202f9a92cd4d

import Definitions.Def_QEC_Locality_CorrectablePartition_EdgeDivision
import Definitions.Def_QEC_Locality_SeparatorProfile_EdgeDivision
set_option autoImplicit false
open QEC QEC.Locality
universe u w
variable {ι : Type u} [Fintype ι] [DecidableEq ι]

theorem solution :
    edgeDivisionSharedBoundary (emptyEdgeRegion (ι := ι)) emptyEdgeActive = ∅ := by
  simp [edgeDivisionSharedBoundary, emptyEdgeActive]
