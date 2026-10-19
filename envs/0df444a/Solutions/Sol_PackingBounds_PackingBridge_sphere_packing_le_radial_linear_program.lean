-- Prove2me | solution 1 for PackingBounds.PackingBridge.sphere_packing_le_radial_linear_program
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:37.283608+00:00
-- url     : https://prove2.me/submissions/375225e4-f81b-468f-863a-f288c1b81b01

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_geometricFactor_pos
import Theorems.Thm_CohnElkies_quotient_pos
import Theorems.Thm_CohnElkies_quotientSet_nonempty
import Theorems.Thm_PackingBounds_PackingBridge_sphere_packing_le_admissible

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
    (SpherePackingConstant d).toReal ≤ CohnElkies.linearProgram d := by
  have hfactor := CohnElkies.geometricFactor_pos d
  have hbound :
      (SpherePackingConstant d).toReal /
          (CohnElkies.unitBallVolume d / (2 : ℝ) ^ d) ≤
        sInf (CohnElkies.quotientSet d) := by
    apply le_csInf (CohnElkies.quotientSet_nonempty d)
    rintro _ ⟨f, rfl⟩
    apply (div_le_iff₀ hfactor).2
    have hcost : 0 ≤
        CohnElkies.unitBallVolume d / (2 : ℝ) ^ d * CohnElkies.quotient f :=
      mul_nonneg hfactor.le (CohnElkies.quotient_pos f).le
    have h := ENNReal.toReal_le_of_le_ofReal hcost
      (sphere_packing_le_admissible hd f)
    simpa [mul_comm] using! h
  unfold CohnElkies.linearProgram
  simpa [mul_comm] using! (div_le_iff₀ hfactor).1 hbound
end PackingBounds.PackingBridge
