-- Prove2me | solution 1 for ThreeSum.LightLocalParameters.program_meets
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T12:17:24.446329+00:00
-- url     : https://prove2.me/submissions/82796969-6cd8-445d-99e9-4483f04f9f28

import Definitions.Def_Submission_ThreeSum_LightLocalCounts
import Definitions.Def_Submission_ThreeSum_LightSelectedPrime
import Definitions.Def_Submission_ThreeSum_LightSmallDivide
import Definitions.Def_Submission_ThreeSum_LightLocalParameters
import Definitions.Def_WeightedCache3SUM_Alias_e2ad5e59f3af6ab7
import Definitions.Def_WeightedCache3SUM_Alias_9f151fd16c06b1ef
import Theorems.Thm_ThreeSum_LightPrimality_Procs_meets
import Definitions.Def_WeightedCache3SUM_Alias_137b880911028d95
import Definitions.Def_WeightedCache3SUM_Alias_a00dee90c4e0ea45
import Definitions.Def_WeightedCache3SUM_Alias_9b3006da0fcbdf4e
import Definitions.Def_WeightedCache3SUM_Alias_276ab4baf5d9c1f3
import Definitions.Def_WeightedCache3SUM_Alias_73246870e6a638ab
import Definitions.Def_WeightedCache3SUM_Alias_8a94481881de516b


set_option autoImplicit false
open ThreeSum ThreeSum.LightLocalParameters
open Light LocalCoverBounds
variable {lim : Limits} {P : Program} {d : ℕ}
namespace ThreeSum.LightLocalParameters
theorem _root_.solution {μ : ℕ → ℤ} {h dst work : ℕ}
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : d+512*h+5 ≤ lim.depth)
    (hout : dst+8 ≤ work) (hspace : space work h ≤ lim.space)
    (hword : (word h : ℤ) ≤ lim.word) :
    Meets lim program 0 d [h,dst,work] μ (time h)
      (fun r μ' => r = (localPrime h : ℤ) ∧ Seg μ' dst (values h) ∧
        KeptBut μ μ' work dst 8) := procs.meets hw hd hout hspace hword
end ThreeSum.LightLocalParameters
