-- Prove2me | solution 1 for TaoFivePrimes.rh_high_height_vertical_center_eval_left_block03
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-15T09:06:54.465446+00:00
-- url     : https://prove2.me/submissions/72e43adf-fdd2-40c2-b602-d980d81e5b4d

import Mathlib
import Definitions.Def_TaoFivePrimes_RHHighVerticalCenterValuesLeft
import Definitions.Def_TaoFivePrimes_RHHighVerticalJetsLeft
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false
theorem solution :
 ((List.range 16).map (fun i=>(List.range 8).map (fun k=>
  let p:=RHHighVerticalCenter.evaluate RHHighVerticalCenterValuesLeft.values (48+i) k
  (p.1/(2:Int)^48,p.2/(2:Int)^48))))=
 ((List.range 16).map (fun i=>(List.range 8).map (fun k=>
  RHHighContourCoefficientData.decode (((((RHHighVerticalJetsLeft.rows)[(8*(48+i)+k)/512]?).getD [])[((8*(48+i)+k)%512)]?).getD 0)))) := by decide +kernel
