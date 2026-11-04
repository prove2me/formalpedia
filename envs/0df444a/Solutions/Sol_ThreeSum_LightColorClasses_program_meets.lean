-- Prove2me | solution 1 for ThreeSum.LightColorClasses.program_meets
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:09:34.499506+00:00
-- url     : https://prove2.me/submissions/fa01f69f-fc42-4b1b-9f09-330b5d98a39a

import Definitions.Def_Submission_ThreeSum_LightColorArray
import Definitions.Def_Submission_ThreeSum_ColorClassLists
import Definitions.Def_Submission_ThreeSum_LightColorClasses
import Definitions.Def_WeightedCache3SUM_Alias_1bc522b5c56beb35
import Definitions.Def_WeightedCache3SUM_Alias_98152438e5b788f3
import Definitions.Def_WeightedCache3SUM_Alias_ec1db2019105351a
import Definitions.Def_WeightedCache3SUM_Alias_5d83a00a3f301eb9
import Definitions.Def_WeightedCache3SUM_Alias_de0ba8c01a8a208c


set_option autoImplicit false
open ThreeSum ThreeSum.LightColorClasses
open Light ColorClassLists
set_option maxHeartbeats 1500000
set_option maxRecDepth 10000
variable {lim : Limits} {P : Program} {d : ℕ}
namespace ThreeSum.LightColorClasses
theorem _root_.solution {src n W colors dst0 dst1 dst2 work U : ℕ} {μ : ℕ → ℤ}
    (p : Coloring.Parameter W) (x : Fin n → ℤ)
    (hw : (lim.space : ℤ) ≤ lim.word) (hn : n ≤ 2^W)
    (hsrc : src+n ≤ colors) (hcolors : colors+n ≤ dst0)
    (h0 : dst0+(n+1) ≤ dst1) (h1 : dst1+(n+1) ≤ dst2) (h2 : dst2+(n+1) ≤ work)
    (hspace : work+(W+1) ≤ lim.space)
    (hword : ((2^(W+1) : ℕ) : ℤ) ≤ lim.word) (hU : (U : ℤ) ≤ lim.word)
    (hd : d+W+3 ≤ lim.depth) (hread : Seg μ src (List.ofFn x))
    (hbound : ∀ i, |x i| ≤ (U : ℤ)) :
    Meets lim program 0 d [src,n,W,p.1.1.val,p.1.2.val,(p.2 (false,false)).val,
      (p.2 (false,true)).val,(p.2 (true,false)).val,(p.2 (true,true)).val,
      colors,dst0,dst1,dst2,work] μ (time W n)
      (fun _ ν => Output p x μ ν colors dst0 dst1 dst2) :=
  programProcs.meets p x hw hn hsrc hcolors h0 h1 h2 hspace hword hU hd hread hbound
end ThreeSum.LightColorClasses
