-- Prove2me | solution 1 for TaoFivePrimes.rh_high_height_vertical_center_eval_right_block03
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-15T11:40:58.896989+00:00
-- url     : https://prove2.me/submissions/2d2903aa-65b5-484a-9c35-115ea43c2d2c

import Mathlib
import Definitions.Def_TaoFivePrimes_RHHighVerticalCenterValuesRight
import Definitions.Def_TaoFivePrimes_RHHighVerticalJetsRight
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false
theorem solution :
 ((List.range 16).map (fun i=>(List.range 8).map (fun k=>
  let p:=RHHighVerticalCenter.evaluate RHHighVerticalCenterValuesRight.values (48+i) k
  (p.1/(2:Int)^48,p.2/(2:Int)^48))))=
 ((List.range 16).map (fun i=>(List.range 8).map (fun k=>
  RHHighContourCoefficientData.decode (((((RHHighVerticalJetsRight.rows)[(8*(48+i)+k)/512]?).getD [])[((8*(48+i)+k)%512)]?).getD 0)))) := by decide +kernel
