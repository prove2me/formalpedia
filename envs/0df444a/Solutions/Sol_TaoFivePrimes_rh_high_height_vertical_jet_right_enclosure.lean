-- Prove2me | solution 1 for TaoFivePrimes.rh_high_height_vertical_jet_right_enclosure
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-15T13:11:48.55599+00:00
-- url     : https://prove2.me/submissions/b2425ab4-bdf2-4380-8bd4-5a2cd63dc9d8

import Mathlib
import Definitions.Def_TaoFivePrimes_RHHighPolynomialJet
import Definitions.Def_TaoFivePrimes_RHHighContourGridV2
import Theorems.Thm_TaoFivePrimes_rh_high_height_center_point_enclosure
import Theorems.Thm_TaoFivePrimes_rh_high_height_vertical_center_right_enclosure
import Theorems.Thm_TaoFivePrimes_rh_high_height_vertical_evaluation_right
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
theorem solution (j k : Nat) (hj:j≤128) (hk:k<8) :
 ‖RHHighPolynomialJet.jet (64+(-1/2+(j:ℂ)/128)*Complex.I) (Complex.I/128) k-
 RHHighContourVector.value (RHHighContourGridV2.vertical true j k)‖≤1/10^12 := by
 have hp:RHHighContourGridV2.vertical true j k=
  ((RHHighVerticalCenter.evaluate RHHighVerticalCenterValuesRight.values j k).1/(2:Int)^48,
   (RHHighVerticalCenter.evaluate RHHighVerticalCenterValuesRight.values j k).2/(2:Int)^48) := by
  simpa only[RHHighContourGridV2.vertical,Bool.false_eq_true,if_false,if_true] using
   (TaoFivePrimes.rh_high_height_vertical_evaluation_right j k hj hk).symm
 have h:=TaoFivePrimes.rh_high_height_center_point_enclosure ⟨2,by decide⟩ RHHighVerticalCenterValuesRight.values
  j k hj hk (fun n hn=>TaoFivePrimes.rh_high_height_vertical_center_right_enclosure n hn)
  (RHHighContourGridV2.vertical true j k) hp
 norm_num only[Fin.val_mk,Nat.cast_ofNat] at h ⊢
 exact h
#print axioms solution
