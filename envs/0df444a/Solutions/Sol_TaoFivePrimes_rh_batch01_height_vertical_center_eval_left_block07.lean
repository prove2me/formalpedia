-- Prove2me | solution 1 for TaoFivePrimes.rh_batch01_height_vertical_center_eval_left_block07
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-16T12:56:47.418028+00:00
-- url     : https://prove2.me/submissions/ba409231-6349-4e48-9792-4406ba168ed1

import Mathlib
import Definitions.Def_TaoFivePrimes_RHBatch01VerticalCenterValuesLeft
import Definitions.Def_TaoFivePrimes_RHBatch01VerticalJetsLeft
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false
theorem solution :
 ((List.range 16).map (fun i=>(List.range 8).map (fun k=>
  let p:=RHBatch01VerticalCenter.evaluate RHBatch01VerticalCenterValuesLeft.values (112+i) k
  (p.1/(2:Int)^48,p.2/(2:Int)^48))))=
 ((List.range 16).map (fun i=>(List.range 8).map (fun k=>
  RHBatch01ContourCoefficientData.decode (((((RHBatch01VerticalJetsLeft.rows)[(8*(112+i)+k)/512]?).getD [])[((8*(112+i)+k)%512)]?).getD 0)))) := by decide +kernel
#print axioms solution
