-- Prove2me | solution 1 for TaoFivePrimes.rh_high_height_vertical_center_eval_left_block00
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-15T08:51:25.029552+00:00
-- url     : https://prove2.me/submissions/0a11cf32-b2c2-4109-babf-5e1ee97ecd9d

import Mathlib
import Definitions.Def_TaoFivePrimes_RHHighVerticalCenterValuesLeft
import Definitions.Def_TaoFivePrimes_RHHighVerticalJetsLeft
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false
theorem solution :
 ((List.range 16).map (fun i=>(List.range 8).map (fun k=>
  let p:=RHHighVerticalCenter.evaluate RHHighVerticalCenterValuesLeft.values (0+i) k
  (p.1/(2:Int)^48,p.2/(2:Int)^48))))=
 ((List.range 16).map (fun i=>(List.range 8).map (fun k=>
  RHHighContourCoefficientData.decode (((((RHHighVerticalJetsLeft.rows)[(8*(0+i)+k)/512]?).getD [])[((8*(0+i)+k)%512)]?).getD 0)))) := by decide +kernel
