-- Prove2me | solution 1 for ThreeSum.LightPairSearch.program_meets
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:25:36.484655+00:00
-- url     : https://prove2.me/submissions/695d8fc7-7300-4987-b21b-191bb5015c8d

import Definitions.Def_Submission_ThreeSum_LightPairSearchMain
import Definitions.Def_Submission_ThreeSum_LightPairSearchProgram
import Theorems.Thm_Light_Ends_append
import Theorems.Thm_Light_Exec_append
import Theorems.Thm_Light_Meets_append
import Theorems.Thm_Light_Meets_mono_time
import Theorems.Thm_Light_sameFrame_cons_cons
import Theorems.Thm_Light_sameFrame_cons_nil
import Theorems.Thm_Light_sameFrame_nil
import Theorems.Thm_Light_sameFrame_nil_cons
import Theorems.Thm_Light_toNat_natCast_add_natCast
import Theorems.Thm_ThreeSumApsp_AbsLe_append
import Theorems.Thm_ThreeSum_LightPairSearch_meets
import Theorems.Thm_ThreeSum_LightPairSearch_time_bound
attribute [local simp] Light.sameFrame_cons_cons
attribute [local simp] Light.sameFrame_cons_nil
attribute [local simp] Light.sameFrame_nil
attribute [local simp] Light.sameFrame_nil_cons
attribute [local simp] Light.toNat_natCast_add_natCast



set_option autoImplicit false
open ThreeSum ThreeSum.LightPairSearch
open Light
variable {lim : Limits}
namespace ThreeSum.LightPairSearch
theorem _root_.solution (predicates : Program) (pPred : ℕ) {q ctx T d : ℕ}
    (good : ℕ → ℕ → Prop) [DecidableRel good] (I : (ℕ → ℤ) → Prop)
    (hq : 0<q) (μ : ℕ → ℤ) (hI : I μ)
    (hword : ((q*q+q+ctx+20 : ℕ) : ℤ) ≤ lim.word)
    (hd : d+1<lim.depth)
    (hpred : ∀ u<q, ∀ v<q, ∀ ν, I ν → Meets lim predicates pPred (d+2) [u,v,ctx] ν T
      (fun r ξ => r=(if good u v then 1 else 0) ∧ I ξ)) :
    Meets lim (program predicates pPred) (predicates.length+1) d [q,ctx] μ
      (q*q*(T+200)+100)
      (fun r ν => r=(first (goodCode q good) (q*q) : ℤ) ∧ I ν) := by
  have hmain : (program predicates pPred)[predicates.length+1]?=some (body predicates.length) := by
    simp [program,List.getElem?_append_right]
  have hrow : (program predicates pPred)[predicates.length]?=some (rowBody pPred) := by
    simp [program,List.getElem?_append_right]
  have hc := meets hmain hrow good I hq μ hI hword hd
    (fun u hu v hv ν hν => (hpred u hu v hv ν hν).append [rowBody pPred,body predicates.length])
  exact hc.mono_time (time_bound q T hq)
end ThreeSum.LightPairSearch
