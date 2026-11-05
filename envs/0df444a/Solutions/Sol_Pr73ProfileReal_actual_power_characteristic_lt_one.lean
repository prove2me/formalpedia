-- Prove2me | solution 1 for Pr73ProfileReal.actual_power_characteristic_lt_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T08:44:21.342874+00:00
-- url     : https://prove2.me/submissions/b4beabd5-8b66-4615-941e-53edd886c9f1

import Definitions.Def_Pr73ProfileCertificate
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Definitions.Def_Pr73ProfileReal
import Theorems.Thm_Pr73ProfileReal_row_valid
import Theorems.Thm_Pr73ProfileReal_real_characteristic_lt_one
import Theorems.Thm_Pr73ProfileReal_power_term_identity

set_option autoImplicit true
open Pr73ProfileReal
open AnalyticEnclosures Pr73ProfileCertificate
namespace Pr73ProfileReal
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
end Pr73ProfileReal
