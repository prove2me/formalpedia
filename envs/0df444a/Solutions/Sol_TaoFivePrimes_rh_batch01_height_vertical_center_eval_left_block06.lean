-- Prove2me | solution 1 for TaoFivePrimes.rh_batch01_height_vertical_center_eval_left_block06
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-16T10:24:24.425584+00:00
-- url     : https://prove2.me/submissions/f3a360da-b8ad-46ef-9a15-042e9a913c11

import Mathlib
import Definitions.Def_TaoFivePrimes_RHBatch01VerticalCenterValuesLeft
import Definitions.Def_TaoFivePrimes_RHBatch01VerticalJetsLeft
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false
theorem solution :
 ((List.range 16).map (fun i=>(List.range 8).map (fun k=>
  let p:=RHBatch01VerticalCenter.evaluate RHBatch01VerticalCenterValuesLeft.values (96+i) k
  (p.1/(2:Int)^48,p.2/(2:Int)^48))))=
 ((List.range 16).map (fun i=>(List.range 8).map (fun k=>
  RHBatch01ContourCoefficientData.decode (((((RHBatch01VerticalJetsLeft.rows)[(8*(96+i)+k)/512]?).getD [])[((8*(96+i)+k)%512)]?).getD 0)))) := by decide +kernel
#print axioms solution
