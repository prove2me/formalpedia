-- Prove2me | solution 1 for SelectedFloorTransfer.all_width_cost_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T08:44:21.154279+00:00
-- url     : https://prove2.me/submissions/bbb1b8b3-8d05-4a68-bfa5-f4489066e79d

import Definitions.Def_FloorRecurrence
import Definitions.Def_SelectedProfileReal
import Definitions.Def_SelectedFloorTransfer
import Theorems.Thm_FloorRecurrence_finite_base_all_width
import Theorems.Thm_SelectedProfileReal_actual_power_characteristic_lt_one
import Theorems.Thm_SelectedProfileReal_row_valid


set_option autoImplicit true
open SelectedFloorTransfer
open SelectedProfileCertificate
namespace SelectedFloorTransfer
theorem _root_.solution (f : ℕ → ℝ) (C : ℝ)
    (physical_recurrence : ∀ e, m ≤ e →
      f e ≤ C + (rows.map (fun r => (r.multiplicity : ℝ) / W *
        f (r.width * (e / m)))).sum) :
    ∀ e, 0 < e → f e ≤ costConstant f C * (e : ℝ) ^ (1 - (saving : ℝ)) := by
  apply FloorRecurrence.finite_base_all_width rows
    (fun r => (r.multiplicity : ℝ) / W) (fun r => r.width) m f
    (1 - (saving : ℝ)) C SelectedProfileReal.powerCharacteristic
  · norm_num [m]
  · norm_num [saving]
  · intro r hr; positivity
  · intro r hr; exact (SelectedProfileReal.row_valid r hr).1
  · intro r hr; exact (SelectedProfileReal.row_valid r hr).2.1
  · rfl
  · exact SelectedProfileReal.actual_power_characteristic_lt_one
  · exact physical_recurrence
end SelectedFloorTransfer
