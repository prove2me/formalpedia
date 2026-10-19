-- Prove2me | solution 1 for SpherePacking.upper_packing_density_le_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:35.874095+00:00
-- url     : https://prove2.me/submissions/8368468f-8adf-41c0-9a4a-5e7b342df8c8

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_SpherePacking_local_density_le_one

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
open MeasureTheory Metric Filter
open Module
open scoped BigOperators ENNReal Pointwise
open SpherePacking
namespace SpherePacking
theorem _root_.solution {d : ℕ} (S : SpherePacking d) : S.upperPackingDensity ≤ 1 := by
  rw [upperPackingDensity]
  exact limsup_le_iSup.trans <| iSup_le fun R => local_density_le_one (S := S) R
end SpherePacking
