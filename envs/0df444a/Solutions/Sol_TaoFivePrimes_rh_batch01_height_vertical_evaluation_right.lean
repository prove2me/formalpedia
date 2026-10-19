-- Prove2me | solution 1 for TaoFivePrimes.rh_batch01_height_vertical_evaluation_right
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-16T13:32:25.780517+00:00
-- url     : https://prove2.me/submissions/a9217a5d-4028-4136-a6f0-1a1c5bd9ef89

import Mathlib
import Definitions.Def_TaoFivePrimes_RHHighContourVector
import Definitions.Def_TaoFivePrimes_RHBatch01VerticalCenterValuesRight
import Definitions.Def_TaoFivePrimes_RHBatch01VerticalJetsRight
import Theorems.Thm_TaoFivePrimes_rh_batch01_height_vertical_center_eval_right_block00
import Theorems.Thm_TaoFivePrimes_rh_batch01_height_vertical_center_eval_right_block01
import Theorems.Thm_TaoFivePrimes_rh_batch01_height_vertical_center_eval_right_block02
import Theorems.Thm_TaoFivePrimes_rh_batch01_height_vertical_center_eval_right_block03
import Theorems.Thm_TaoFivePrimes_rh_batch01_height_vertical_center_eval_right_block04
import Theorems.Thm_TaoFivePrimes_rh_batch01_height_vertical_center_eval_right_block05
import Theorems.Thm_TaoFivePrimes_rh_batch01_height_vertical_center_eval_right_block06
import Theorems.Thm_TaoFivePrimes_rh_batch01_height_vertical_center_eval_right_block07
import Theorems.Thm_TaoFivePrimes_rh_batch01_height_vertical_center_eval_right_block08
namespace RHBatch01VerticalEvaluationRight
lemma map_at {α : Type} (f : Nat→α) (d : α) (N i : Nat) (hi:i<N) :
 (((List.range N).map f)[i]?).getD d=f i := by
 rw[List.getElem?_eq_getElem (by simp only[List.length_map,List.length_range];exact hi),Option.getD_some,
  List.getElem_map,List.getElem_range]
end RHBatch01VerticalEvaluationRight
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
theorem solution (j k : Nat) (hj:j≤128) (hk:k<8) :
 let p:=RHBatch01VerticalCenter.evaluate RHBatch01VerticalCenterValuesRight.values j k
 (p.1/(2:Int)^48,p.2/(2:Int)^48)=RHHighContourVector.decode
  (((((RHBatch01VerticalJetsRight.rows)[(8*j+k)/512]?).getD [])[((8*j+k)%512)]?).getD 0) := by
 let b:=j/16
 let i:=j%16
 have hb:b<9:=by dsimp[b];omega
 have he:16*b+i=j:=by dsimp[b,i];omega
 interval_cases b
 · have hi:i<16:=by dsimp[i] at *;omega
   have h:=TaoFivePrimes.rh_batch01_height_vertical_center_eval_right_block00
   have hh:=congrArg (fun xs:List (List (Int×Int))=>(((xs[i]?).getD [])[k]?).getD (0,0)) h
   simp only[RHBatch01VerticalEvaluationRight.map_at _ _ 16 i hi,RHBatch01VerticalEvaluationRight.map_at _ _ 8 k hk] at hh
   have he':0+i=j:=by omega
   rw[he'] at hh
   exact hh
 · have hi:i<16:=by dsimp[i] at *;omega
   have h:=TaoFivePrimes.rh_batch01_height_vertical_center_eval_right_block01
   have hh:=congrArg (fun xs:List (List (Int×Int))=>(((xs[i]?).getD [])[k]?).getD (0,0)) h
   simp only[RHBatch01VerticalEvaluationRight.map_at _ _ 16 i hi,RHBatch01VerticalEvaluationRight.map_at _ _ 8 k hk] at hh
   have he':16+i=j:=by omega
   rw[he'] at hh
   exact hh
 · have hi:i<16:=by dsimp[i] at *;omega
   have h:=TaoFivePrimes.rh_batch01_height_vertical_center_eval_right_block02
   have hh:=congrArg (fun xs:List (List (Int×Int))=>(((xs[i]?).getD [])[k]?).getD (0,0)) h
   simp only[RHBatch01VerticalEvaluationRight.map_at _ _ 16 i hi,RHBatch01VerticalEvaluationRight.map_at _ _ 8 k hk] at hh
   have he':32+i=j:=by omega
   rw[he'] at hh
   exact hh
 · have hi:i<16:=by dsimp[i] at *;omega
   have h:=TaoFivePrimes.rh_batch01_height_vertical_center_eval_right_block03
   have hh:=congrArg (fun xs:List (List (Int×Int))=>(((xs[i]?).getD [])[k]?).getD (0,0)) h
   simp only[RHBatch01VerticalEvaluationRight.map_at _ _ 16 i hi,RHBatch01VerticalEvaluationRight.map_at _ _ 8 k hk] at hh
   have he':48+i=j:=by omega
   rw[he'] at hh
   exact hh
 · have hi:i<16:=by dsimp[i] at *;omega
   have h:=TaoFivePrimes.rh_batch01_height_vertical_center_eval_right_block04
   have hh:=congrArg (fun xs:List (List (Int×Int))=>(((xs[i]?).getD [])[k]?).getD (0,0)) h
   simp only[RHBatch01VerticalEvaluationRight.map_at _ _ 16 i hi,RHBatch01VerticalEvaluationRight.map_at _ _ 8 k hk] at hh
   have he':64+i=j:=by omega
   rw[he'] at hh
   exact hh
 · have hi:i<16:=by dsimp[i] at *;omega
   have h:=TaoFivePrimes.rh_batch01_height_vertical_center_eval_right_block05
   have hh:=congrArg (fun xs:List (List (Int×Int))=>(((xs[i]?).getD [])[k]?).getD (0,0)) h
   simp only[RHBatch01VerticalEvaluationRight.map_at _ _ 16 i hi,RHBatch01VerticalEvaluationRight.map_at _ _ 8 k hk] at hh
   have he':80+i=j:=by omega
   rw[he'] at hh
   exact hh
 · have hi:i<16:=by dsimp[i] at *;omega
   have h:=TaoFivePrimes.rh_batch01_height_vertical_center_eval_right_block06
   have hh:=congrArg (fun xs:List (List (Int×Int))=>(((xs[i]?).getD [])[k]?).getD (0,0)) h
   simp only[RHBatch01VerticalEvaluationRight.map_at _ _ 16 i hi,RHBatch01VerticalEvaluationRight.map_at _ _ 8 k hk] at hh
   have he':96+i=j:=by omega
   rw[he'] at hh
   exact hh
 · have hi:i<16:=by dsimp[i] at *;omega
   have h:=TaoFivePrimes.rh_batch01_height_vertical_center_eval_right_block07
   have hh:=congrArg (fun xs:List (List (Int×Int))=>(((xs[i]?).getD [])[k]?).getD (0,0)) h
   simp only[RHBatch01VerticalEvaluationRight.map_at _ _ 16 i hi,RHBatch01VerticalEvaluationRight.map_at _ _ 8 k hk] at hh
   have he':112+i=j:=by omega
   rw[he'] at hh
   exact hh
 · have hi:i<1:=by dsimp[i] at *;omega
   have h:=TaoFivePrimes.rh_batch01_height_vertical_center_eval_right_block08
   have hh:=congrArg (fun xs:List (List (Int×Int))=>(((xs[i]?).getD [])[k]?).getD (0,0)) h
   simp only[RHBatch01VerticalEvaluationRight.map_at _ _ 1 i hi,RHBatch01VerticalEvaluationRight.map_at _ _ 8 k hk] at hh
   have he':128+i=j:=by omega
   rw[he'] at hh
   exact hh
#print axioms solution
