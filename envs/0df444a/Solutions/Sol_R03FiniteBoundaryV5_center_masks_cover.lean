-- Prove2me | solution 1 for R03FiniteBoundaryV5.center_masks_cover
-- status  : ACCEPTED   (prove)
-- author  : @hao jia
-- created : 2026-09-17T10:27:31.600584+00:00
-- url     : https://prove2.me/submissions/3f018895-4b63-415b-952c-3c1e6ba0f400

import Mathlib.Data.Fin.VecNotation
import Definitions.Def_r03_defs_308a4c5b4d_v5_FiniteBoundary

/- Candidate finite catalogue; no graph-level semantics or admission. -/
namespace R03FiniteBoundaryV5
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

theorem leaf_masks_cover : ∀ m : Fin 32, ones m.val ≤ 2 → ∃ i : Fin 16, leafMasks i = m.val := by
  decide +kernel


end R03FiniteBoundaryV5

open R03FiniteBoundaryV5
theorem solution : ∀ m : Fin 32, ones m.val ≤ 1 → ∃ i : Fin 6, centerMasks i = m.val := by
  decide +kernel
