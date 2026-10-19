-- Prove2me | solution 1 for SpherePacking.packingConstant_eq_SpherePackingConstant
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:32.916513+00:00
-- url     : https://prove2.me/submissions/89985496-dc3b-4672-98ec-bb2eec5e1768

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_SpherePacking_UnitPacking_toGeneralPacking_density
import Theorems.Thm_SpherePacking_UnitPacking_ofGeneralPacking_upperDensity

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open Filter MeasureTheory Metric
open scoped ENNReal Pointwise
open SpherePacking
namespace SpherePacking
theorem _root_.solution (n : ℕ) :
    packingConstant n = _root_.SpherePackingConstant n := by
  unfold packingConstant _root_.SpherePackingConstant
  apply le_antisymm
  · refine iSup_le fun P => ?_
    rw [← P.toGeneralPacking_density]
    exact le_iSup (fun S : _root_.SpherePacking n => S.upperPackingDensity)
      P.toGeneralPacking
  · refine iSup_le fun S => ?_
    rw [← UnitPacking.ofGeneralPacking_upperDensity S]
    exact le_iSup (fun P : UnitPacking n => upperDensity P)
      (UnitPacking.ofGeneralPacking S)
end SpherePacking
