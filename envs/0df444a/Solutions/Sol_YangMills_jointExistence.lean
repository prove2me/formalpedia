-- Prove2me | solution 1 for YangMills.jointExistence
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @LG
-- created : 2026-11-20T17:34:06.185705+00:00
-- url     : https://prove2.me/submissions/18a28cfd-ab37-40e0-9ab3-6ad8c0fccb80
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_YM_canonicalFamily
import Theorems.Thm_YangMills_canonicalFamily_regular
import Theorems.Thm_YangMills_canonicalFamily_core

/-- Joint existence, reduced to Wilson regularity and the continuum core on the
canonical Wilson family. -/
theorem solution : YangMills.JointExistence := by
  intro g hg
  refine ⟨YangMills.canonicalFamily g, YangMills.canonicalFamily_regular g, ?_⟩
  exact YangMills.canonicalFamily_core g hg
