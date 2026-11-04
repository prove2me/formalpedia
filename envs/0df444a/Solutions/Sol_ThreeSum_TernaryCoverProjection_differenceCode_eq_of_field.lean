-- Prove2me | solution 1 for ThreeSum.TernaryCoverProjection.differenceCode_eq_of_field
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:59:37.26287+00:00
-- url     : https://prove2.me/submissions/aa6ceea2-f50d-4b1b-8308-cbdd4a1f4bc7

import Definitions.Def_Submission_ThreeSum_TernaryCoverLocal
import Mathlib.Data.Finset.Powerset
import Definitions.Def_Submission_ThreeSum_TernaryCoverProjection
import Theorems.Thm_ThreeSum_TernaryCoverProjection_differenceCode_lt
import Theorems.Thm_ThreeSum_TernaryCoverProjection_differenceCode_cast
import Theorems.Thm_ThreeSum_HashFamily_hashMap_apply
attribute [local simp] ThreeSum.HashFamily.hashMap_apply



set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryCoverProjection
open Finset TernaryJointType TernaryCoverLocal
namespace ThreeSum.TernaryCoverProjection
theorem _root_.solution {p : ℕ} (hp : 4 < p) (a b c d : Fin 3)
    (heq : (a.val : ZMod p) - (b.val : ZMod p) =
      (c.val : ZMod p) - (d.val : ZMod p)) :
    differenceCode a b = differenceCode c d := by
  have ha : differenceCode a b < p := (differenceCode_lt a b).trans_le (by omega)
  have hc : differenceCode c d < p := (differenceCode_lt c d).trans_le (by omega)
  have he : (differenceCode a b : ZMod p) = (differenceCode c d : ZMod p) := by
    rw [differenceCode_cast, differenceCode_cast, heq]
  have hv := congrArg ZMod.val he
  simpa only [ZMod.val_natCast_of_lt ha, ZMod.val_natCast_of_lt hc] using hv
end ThreeSum.TernaryCoverProjection
