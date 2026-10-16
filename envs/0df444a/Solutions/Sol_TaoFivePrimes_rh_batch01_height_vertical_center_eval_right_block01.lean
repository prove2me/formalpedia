-- Prove2me | solution 1 for TaoFivePrimes.rh_batch01_height_vertical_center_eval_right_block01
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-15T22:29:47.702833+00:00
-- url     : https://prove2.me/submissions/a465f887-74f7-450a-9593-cd8c8c0da8f2

import Mathlib
import Definitions.Def_TaoFivePrimes_RHBatch01VerticalCenterValuesRight
import Definitions.Def_TaoFivePrimes_RHBatch01VerticalJetsRight
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false
theorem solution :
 ((List.range 16).map (fun i=>(List.range 8).map (fun k=>
  let p:=RHBatch01VerticalCenter.evaluate RHBatch01VerticalCenterValuesRight.values (16+i) k
  (p.1/(2:Int)^48,p.2/(2:Int)^48))))=
 ((List.range 16).map (fun i=>(List.range 8).map (fun k=>
  RHBatch01ContourCoefficientData.decode (((((RHBatch01VerticalJetsRight.rows)[(8*(16+i)+k)/512]?).getD [])[((8*(16+i)+k)%512)]?).getD 0)))) := by decide +kernel
#print axioms solution
