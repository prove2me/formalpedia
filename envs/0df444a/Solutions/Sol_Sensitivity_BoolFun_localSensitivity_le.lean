-- Prove2me | solution 1 for Sensitivity.BoolFun.localSensitivity_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T19:12:07.969935+00:00
-- url     : https://prove2.me/submissions/38bdc875-eff7-44be-ac1e-c8c40a91d7c2

import Definitions.Def_Sensitivity_Defs
import Definitions.Def_Sensitivity_Basic

set_option autoImplicit false
open Sensitivity
variable {n : ℕ}
namespace Sensitivity
namespace BoolFun
theorem _root_.solution (f : BoolFun n) (x : Fin n → Bool) :
    f.localSensitivity x ≤ n := by
  unfold localSensitivity
  calc (Finset.univ.filter fun i => f.sensitiveAt x i).card
      ≤ Finset.univ.card := Finset.card_filter_le _ _
    _ = n := Finset.card_fin n
end BoolFun
end Sensitivity
