-- Prove2me | solution 1 for SpherePacking.packing_supremum_eq_unit_separation
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:35.874095+00:00
-- url     : https://prove2.me/submissions/5af47c67-d1d0-4e30-8367-c5b07d8b6e16

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_SpherePacking_rescale_upper_packing_density

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
open MeasureTheory Metric Filter
open Module
open scoped BigOperators ENNReal Pointwise
open SpherePacking
namespace SpherePacking
theorem _root_.solution {d : ℕ} :
    SpherePackingConstant d = ⨆ (S : SpherePacking d) (_ : S.separation = 1), S.upperPackingDensity := by
  rw [iSup_subtype', SpherePackingConstant]
  refine le_antisymm (iSup_le ?_) (iSup_le ?_)
  · intro S
    simpa [rescale_upper_packing_density] using!
      (le_iSup (fun S : { S : SpherePacking d // S.separation = 1 } ↦ S.val.upperPackingDensity)
        ⟨S.rescaleConfiguration (inv_pos.mpr S.separation_pos), inv_mul_cancel₀ S.separation_pos.ne.symm⟩)
  · rintro ⟨S, -⟩
    exact le_iSup upperPackingDensity S
end SpherePacking
