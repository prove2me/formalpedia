-- Prove2me | solution 1 for ThreeSum.LightWeightDecode.program_meets
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:50:49.607778+00:00
-- url     : https://prove2.me/submissions/55927357-38d5-45ed-bf27-22e880536de5

import Definitions.Def_Submission_ThreeSum_LightWeightRow
import Definitions.Def_Submission_ThreeSum_LightWeightDecode
import Definitions.Def_WeightedCache3SUM_Alias_de9d37b5900d1a92
import Definitions.Def_WeightedCache3SUM_Alias_e6a24ed55341e959
import Definitions.Def_WeightedCache3SUM_Alias_73246870e6a638ab
import Definitions.Def_WeightedCache3SUM_Alias_b5410f4bcc10d599


set_option autoImplicit false
open ThreeSum ThreeSum.LightWeightDecode
open Light
variable {lim : Limits} {P : Program} {d : ℕ}
namespace ThreeSum.LightWeightDecode
theorem _root_.solution
    {μ : ℕ → ℤ} {L p k dst work : ℕ}
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : d+2 < lim.depth) (hp : 1 ≤ p)
    (hdst : dst+2*L ≤ work) (hspace : work+(2*L+1) ≤ lim.space)
    (hword : (word L p k : ℤ) ≤ lim.word) :
    Meets lim program 0 d [L,p,k,dst,work] μ (time L k)
      (fun _ μ' => Rows μ' dst L p k ∧
        (∀ e ≤ 2*L, μ' (work+e) = ((p^e : ℕ) : ℤ)) ∧
        KeptBut μ μ' work dst (2*L)) :=
  programProcs.meets hw hd hp hdst hspace hword
end ThreeSum.LightWeightDecode
