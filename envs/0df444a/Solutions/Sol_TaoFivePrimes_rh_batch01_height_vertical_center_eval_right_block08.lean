-- Prove2me | solution 1 for TaoFivePrimes.rh_batch01_height_vertical_center_eval_right_block08
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-16T13:16:14.192315+00:00
-- url     : https://prove2.me/submissions/2b24ca64-319e-456f-bba4-afe139fe6087

import Mathlib
import Definitions.Def_TaoFivePrimes_RHBatch01VerticalCenterValuesRight
import Definitions.Def_TaoFivePrimes_RHBatch01VerticalJetsRight
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false
theorem solution :
 ((List.range 1).map (fun i=>(List.range 8).map (fun k=>
  let p:=RHBatch01VerticalCenter.evaluate RHBatch01VerticalCenterValuesRight.values (128+i) k
  (p.1/(2:Int)^48,p.2/(2:Int)^48))))=
 ((List.range 1).map (fun i=>(List.range 8).map (fun k=>
  RHBatch01ContourCoefficientData.decode (((((RHBatch01VerticalJetsRight.rows)[(8*(128+i)+k)/512]?).getD [])[((8*(128+i)+k)%512)]?).getD 0)))) := by decide +kernel
#print axioms solution
