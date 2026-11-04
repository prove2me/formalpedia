-- Prove2me | solution 1 for ThreeSum.LightColorArray.program_meets
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:54:13.932349+00:00
-- url     : https://prove2.me/submissions/e78dcf6a-a75c-4f11-afdd-d662588fe9a5

import Definitions.Def_Submission_ThreeSum_LightColorIndex
import Definitions.Def_Submission_ThreeSum_LightSubsetAddress
import Definitions.Def_Submission_ThreeSum_LightColorArray
import Definitions.Def_WeightedCache3SUM_Alias_ec1db2019105351a
import Definitions.Def_WeightedCache3SUM_Alias_5d83a00a3f301eb9
import Definitions.Def_WeightedCache3SUM_Alias_de0ba8c01a8a208c


set_option autoImplicit false
open ThreeSum ThreeSum.LightColorArray
open Light LightSubsetAddress
set_option maxHeartbeats 1200000
variable {lim : Limits} {P : Program} {d : ℕ}
namespace ThreeSum.LightColorArray
theorem _root_.solution {W n dst work : ℕ} (μ : ℕ → ℤ) (p : Coloring.Parameter W)
    (hw : (lim.space : ℤ) ≤ lim.word) (hn : n ≤ 2^W)
    (hdst : dst+n ≤ work) (hspace : work+(W+1) ≤ lim.space)
    (hword : ((2^(W+1) : ℕ) : ℤ) ≤ lim.word) (hd : d+W+2 ≤ lim.depth) :
    Meets lim program 0 d [W,n,p.1.1.val,p.1.2.val,(p.2 (false,false)).val,
      (p.2 (false,true)).val,(p.2 (true,false)).val,(p.2 (true,true)).val,dst,work]
      μ (time W n) (fun _ ν =>
        (∀ i < n, ν (dst+i) = (LightColorIndex.color p i : ℤ)) ∧
        Powers ν work W ∧ KeptBut μ ν work dst n) :=
  meets rfl rfl rfl rfl μ p hw hn hdst hspace hword hd
end ThreeSum.LightColorArray
