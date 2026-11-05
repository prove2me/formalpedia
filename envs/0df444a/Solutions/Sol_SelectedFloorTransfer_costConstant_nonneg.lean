-- Prove2me | solution 1 for SelectedFloorTransfer.costConstant_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T08:44:21.154279+00:00
-- url     : https://prove2.me/submissions/c646b427-f504-4869-be7e-c7bb06fc2d6b

import Definitions.Def_FloorRecurrence
import Definitions.Def_SelectedProfileReal
import Definitions.Def_SelectedFloorTransfer
import Theorems.Thm_FloorRecurrence_boundConstant_nonneg
import Theorems.Thm_SelectedProfileReal_actual_power_characteristic_lt_one


set_option autoImplicit true
open SelectedFloorTransfer
open SelectedProfileCertificate
namespace SelectedFloorTransfer
theorem _root_.solution (f : ℕ → ℝ) (C : ℝ) : 0 ≤ costConstant f C :=
  FloorRecurrence.boundConstant_nonneg m f C SelectedProfileReal.powerCharacteristic
    SelectedProfileReal.actual_power_characteristic_lt_one
end SelectedFloorTransfer
