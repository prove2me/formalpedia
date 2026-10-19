-- Prove2me | solution 1 for PackingBounds.PackingBridge.sphere_packing_le_radial_linear_program_ennreal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:37.283608+00:00
-- url     : https://prove2.me/submissions/626f4c23-f174-4c62-aabf-f60681d24660

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_linearProgram_nonneg
import Theorems.Thm_SpherePacking_upper_packing_density_le_one
import Theorems.Thm_PackingBounds_PackingBridge_sphere_packing_le_radial_linear_program

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Metric
open scoped ENNReal FourierTransform SchwartzMap Topology
open PackingBounds PackingBounds.PackingBridge
namespace PackingBounds.PackingBridge
theorem _root_.solution
    {d : ℕ} (hd : 0 < d) :
    SpherePackingConstant d ≤ ENNReal.ofReal (CohnElkies.linearProgram d) := by
  have hfinite : SpherePackingConstant d ≠ ⊤ := by
    apply ne_top_of_le_ne_top ENNReal.one_ne_top
    unfold SpherePackingConstant
    exact iSup_le fun P => SpherePacking.upper_packing_density_le_one P
  exact (ENNReal.le_ofReal_iff_toReal_le hfinite
    (CohnElkies.linearProgram_nonneg d)).2
      (sphere_packing_le_radial_linear_program hd)
end PackingBounds.PackingBridge
