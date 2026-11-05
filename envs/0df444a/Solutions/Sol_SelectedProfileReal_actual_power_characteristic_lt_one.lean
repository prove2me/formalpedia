-- Prove2me | solution 1 for SelectedProfileReal.actual_power_characteristic_lt_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T08:44:21.154279+00:00
-- url     : https://prove2.me/submissions/1b5d20a4-2992-4109-a5f3-0d624391e74f

import Definitions.Def_SelectedProfileCertificate
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Definitions.Def_SelectedProfileReal
import Theorems.Thm_SelectedProfileReal_row_valid
import Theorems.Thm_SelectedProfileReal_real_characteristic_lt_one
import Theorems.Thm_SelectedProfileReal_power_term_identity

set_option autoImplicit true
open SelectedProfileReal
open AnalyticEnclosures SelectedProfileCertificate
namespace SelectedProfileReal
theorem _root_.solution : powerCharacteristic < 1 := by
  have heq : powerCharacteristic = exponentialCharacteristic := by
    unfold powerCharacteristic exponentialCharacteristic
    congr 1
    apply List.map_congr_left
    intro r hr
    rw [power_term_identity _ _ _ _ _ (by exact_mod_cast (row_valid r hr).1) (by norm_num [m])]
    simp [weight]
  rw [heq]
  exact real_characteristic_lt_one
end SelectedProfileReal
