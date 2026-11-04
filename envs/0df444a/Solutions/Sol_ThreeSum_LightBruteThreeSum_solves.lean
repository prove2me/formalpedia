-- Prove2me | solution 1 for ThreeSum.LightBruteThreeSum.solves
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:58:57.16325+00:00
-- url     : https://prove2.me/submissions/29b486aa-db53-4d0b-a36a-3039dcba4518

import Definitions.Def_Submission_ThreeSum_LightOriginalTripleScan
import Definitions.Def_Submission_ThreeSum_OriginalThreeSum
import Definitions.Def_Submission_ThreeSum_LightBruteThreeSum
import Definitions.Def_WeightedCache3SUM_Alias_1b87db5b0e9f9b11
import Theorems.Thm_Light_ArrayAt_mono
import Theorems.Thm_Light_Ends_mono
import Theorems.Thm_Light_ListAt_mono
import Theorems.Thm_Light_Meets_mono
import Theorems.Thm_Light_Need_Ok_mono
import Theorems.Thm_Light_SameOn_mono
import Theorems.Thm_Light_SameOn_refl
import Theorems.Thm_Light_SameOutside2_refl
import Theorems.Thm_Light_SameOutside_mono
import Theorems.Thm_Light_SameOutside_refl
import Theorems.Thm_Light_SolvedIn_mono
import Theorems.Thm_Light_SolvesN_meets
import Theorems.Thm_Light_Solves_meets
import Theorems.Thm_Light_TriInst_Pre_mono
import Theorems.Thm_P2M_Light_getElem__append_of_eq_some_9fa037aa12b5
import Definitions.Def_WeightedCache3SUM_Alias_98152438e5b788f3
import Definitions.Def_WeightedCache3SUM_Alias_5d83a00a3f301eb9
import Definitions.Def_WeightedCache3SUM_Alias_6cd6f72823a59258
import Definitions.Def_WeightedCache3SUM_Alias_de0ba8c01a8a208c
import Definitions.Def_WeightedCache3SUM_Alias_ec604c008ed4b1df
import Definitions.Def_WeightedCache3SUM_Alias_eb09b223848624eb
import Definitions.Def_WeightedCache3SUM_Alias_73246870e6a638ab
import Theorems.Thm_ThreeSum_OriginalThreeSum_task_bound
import Theorems.Thm_ThreeSum_OriginalThreeSum_task_post
import Theorems.Thm_ThreeSum_OriginalThreeSum_task_read


set_option autoImplicit false
open ThreeSum ThreeSum.LightBruteThreeSum
open Light ThreeSumApsp.Spec
set_option maxHeartbeats 1800000
set_option maxRecDepth 10000
variable {lim : Limits} {P : Program}
namespace ThreeSum.LightBruteThreeSum
theorem _root_.solution : Solves s3Task program 3 (fun n _ => time n) need := by
  refine ⟨body 2,rfl,fun R lim d x μ fr H hok => ?_⟩
  have hp : (program++R)[3]?=some (body 2) := getElem?_append_of_eq_some (by rfl) R
  have hs : (program++R)[2]?=some (LightOriginalTripleScan.body 2 0) := getElem?_append_of_eq_some (by rfl) R
  have hr : (program++R)[0]?=some (LightOriginalTripleRow.body 1) := getElem?_append_of_eq_some (by rfl) R
  have hv : (program++R)[1]?=some LightSmallDivide.body := getElem?_append_of_eq_some (by rfl) R
  have hh := meets (P := program++R) (pMain := 3) (d := d) (vecOf x.N x.X) μ hp hs hr hv
    H.N_pos H.below hok (OriginalThreeSum.task_read H) (OriginalThreeSum.task_bound H)
  obtain ⟨b,hb,he⟩ := hh.mono le_rfl (fun r ν ⟨hbool,hcorrect,hmem⟩ =>
    OriginalThreeSum.task_post (x := x) (μ := μ) (ν := ν) (fr := fr)
      hbool hcorrect (by subst ν; exact SameOn.refl))
  have heq : b=body 2 := Option.some.inj (hb.symm.trans hp)
  subst b
  exact he
end ThreeSum.LightBruteThreeSum
