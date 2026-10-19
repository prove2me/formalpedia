-- Prove2me | solution 1 for SpherePacking.local_density_le_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:35.874095+00:00
-- url     : https://prove2.me/submissions/77e45d27-4915-4fed-a16f-6dbd6947537d

import Mathlib
import Definitions.Def_SpherePacking

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
open MeasureTheory Metric Filter
open Module
open scoped BigOperators ENNReal Pointwise
open SpherePacking
namespace SpherePacking
theorem _root_.solution {d : ℕ} (S : SpherePacking d) (R : ℝ) :
    S.densityInsideRadius R ≤ 1 := by
  simpa [densityInsideRadius] using!
    (ENNReal.div_le_of_le_mul (by simpa [one_mul] using! volume.mono Set.inter_subset_right))
end SpherePacking
