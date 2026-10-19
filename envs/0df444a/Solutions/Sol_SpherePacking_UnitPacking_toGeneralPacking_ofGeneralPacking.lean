-- Prove2me | solution 1 for SpherePacking.UnitPacking.toGeneralPacking_ofGeneralPacking
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:32.916513+00:00
-- url     : https://prove2.me/submissions/a46b778f-948b-4ae2-aea3-ba4463ea0125

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open Filter MeasureTheory Metric
open scoped ENNReal Pointwise
open SpherePacking
namespace SpherePacking
namespace UnitPacking
theorem _root_.solution {n : ℕ}
    (S : _root_.SpherePacking n) :
    (UnitPacking.ofGeneralPacking S).toGeneralPacking =
      S.rescaleConfiguration (c := 2 / S.separation)
        (div_pos (by norm_num : (0 : ℝ) < 2) S.separation_pos) := by
  dsimp [UnitPacking.ofGeneralPacking, UnitPacking.toGeneralPacking,
    _root_.SpherePacking.rescaleConfiguration]
  simp only [div_mul_cancel₀ 2 S.separation_pos.ne']
end UnitPacking
end SpherePacking
