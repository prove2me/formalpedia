-- Prove2me | solution 1 for TaoFivePrimes.rh_batch01_height_vertical_jet_left_enclosure
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-16T13:38:07.316758+00:00
-- url     : https://prove2.me/submissions/0b58407d-8323-4012-ac6f-fba89d3dc2d0

import Mathlib
import Definitions.Def_TaoFivePrimes_RHBatch01PolynomialJet
import Definitions.Def_TaoFivePrimes_RHBatch01ContourGridV2
import Theorems.Thm_TaoFivePrimes_rh_batch01_height_center_point_enclosure
import Theorems.Thm_TaoFivePrimes_rh_batch01_height_vertical_center_left_enclosure
import Theorems.Thm_TaoFivePrimes_rh_batch01_height_vertical_evaluation_left
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
theorem solution (j k : Nat) (hj:j≤128) (hk:k<8) :
 ‖RHBatch01PolynomialJet.jet (-64+(-1/2+(j:ℂ)/128)*Complex.I) (Complex.I/128) k-
 RHHighContourVector.value (RHBatch01ContourGridV2.vertical false j k)‖≤1/10^12 := by
 have hp:RHBatch01ContourGridV2.vertical false j k=
  ((RHBatch01VerticalCenter.evaluate RHBatch01VerticalCenterValuesLeft.values j k).1/(2:Int)^48,
   (RHBatch01VerticalCenter.evaluate RHBatch01VerticalCenterValuesLeft.values j k).2/(2:Int)^48) := by
  simpa only[RHBatch01ContourGridV2.vertical,Bool.false_eq_true,if_false,if_true] using
   (TaoFivePrimes.rh_batch01_height_vertical_evaluation_left j k hj hk).symm
 have h:=TaoFivePrimes.rh_batch01_height_center_point_enclosure ⟨0,by decide⟩ RHBatch01VerticalCenterValuesLeft.values
  j k hj hk (fun n hn=>TaoFivePrimes.rh_batch01_height_vertical_center_left_enclosure n hn)
  (RHBatch01ContourGridV2.vertical false j k) hp
 norm_num only[Fin.val_mk,Nat.cast_ofNat] at h ⊢
 exact h
#print axioms solution
