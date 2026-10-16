-- Prove2me | solution 1 for TaoFivePrimes.rh_high_height_vertical_center_eval_right_block02
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-15T11:03:29.689986+00:00
-- url     : https://prove2.me/submissions/d7a5a510-c1ec-450c-930a-a5c2ab30373c

import Mathlib
import Definitions.Def_TaoFivePrimes_RHHighVerticalCenterValuesRight
import Definitions.Def_TaoFivePrimes_RHHighVerticalJetsRight
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false
theorem solution :
 ((List.range 16).map (fun i=>(List.range 8).map (fun k=>
  let p:=RHHighVerticalCenter.evaluate RHHighVerticalCenterValuesRight.values (32+i) k
  (p.1/(2:Int)^48,p.2/(2:Int)^48))))=
 ((List.range 16).map (fun i=>(List.range 8).map (fun k=>
  RHHighContourCoefficientData.decode (((((RHHighVerticalJetsRight.rows)[(8*(32+i)+k)/512]?).getD [])[((8*(32+i)+k)%512)]?).getD 0)))) := by decide +kernel
