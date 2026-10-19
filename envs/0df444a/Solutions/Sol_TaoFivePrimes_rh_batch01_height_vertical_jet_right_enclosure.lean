-- Prove2me | solution 1 for TaoFivePrimes.rh_batch01_height_vertical_jet_right_enclosure
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-16T13:43:50.80508+00:00
-- url     : https://prove2.me/submissions/768cfd09-f561-46f0-bdec-9c358b62245e

import Mathlib
import Definitions.Def_TaoFivePrimes_RHBatch01PolynomialJet
import Definitions.Def_TaoFivePrimes_RHBatch01ContourGridV2
import Theorems.Thm_TaoFivePrimes_rh_batch01_height_center_point_enclosure
import Theorems.Thm_TaoFivePrimes_rh_batch01_height_vertical_center_right_enclosure
import Theorems.Thm_TaoFivePrimes_rh_batch01_height_vertical_evaluation_right
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
theorem solution (j k : Nat) (hj:j≤128) (hk:k<8) :
 ‖RHBatch01PolynomialJet.jet (64+(-1/2+(j:ℂ)/128)*Complex.I) (Complex.I/128) k-
 RHHighContourVector.value (RHBatch01ContourGridV2.vertical true j k)‖≤1/10^12 := by
 have hp:RHBatch01ContourGridV2.vertical true j k=
  ((RHBatch01VerticalCenter.evaluate RHBatch01VerticalCenterValuesRight.values j k).1/(2:Int)^48,
   (RHBatch01VerticalCenter.evaluate RHBatch01VerticalCenterValuesRight.values j k).2/(2:Int)^48) := by
  simpa only[RHBatch01ContourGridV2.vertical,Bool.false_eq_true,if_false,if_true] using
   (TaoFivePrimes.rh_batch01_height_vertical_evaluation_right j k hj hk).symm
 have h:=TaoFivePrimes.rh_batch01_height_center_point_enclosure ⟨2,by decide⟩ RHBatch01VerticalCenterValuesRight.values
  j k hj hk (fun n hn=>TaoFivePrimes.rh_batch01_height_vertical_center_right_enclosure n hn)
  (RHBatch01ContourGridV2.vertical true j k) hp
 norm_num only[Fin.val_mk,Nat.cast_ofNat] at h ⊢
 exact h
#print axioms solution
