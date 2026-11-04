-- Prove2me | solution 1 for ThreeSum.LightLocalCounts.program_meets
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:59:15.168038+00:00
-- url     : https://prove2.me/submissions/0e55164d-33ee-4370-bacc-adb783da2b58

import Definitions.Def_Submission_ThreeSum_LightSubsetSetup
import Definitions.Def_Submission_ThreeSum_LocalCoverBounds
import Definitions.Def_Submission_ThreeSum_LightLocalCounts
import Definitions.Def_WeightedCache3SUM_Alias_9f151fd16c06b1ef
import Definitions.Def_WeightedCache3SUM_Alias_8a94481881de516b


set_option autoImplicit false
open ThreeSum ThreeSum.LightLocalCounts
set_option maxHeartbeats 1000000
set_option maxRecDepth 4000
open Light LocalCoverBounds LightPascal LightSubsetAddress
variable {lim : Limits} {P : Program} {d : ℕ}
namespace ThreeSum.LightLocalCounts
theorem _root_.solution {μ : ℕ → ℤ} {h dst work : ℕ}
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : d+512*h+4 ≤ lim.depth)
    (hout : dst+6 ≤ work) (hspace : space work h ≤ lim.space)
    (hword : (word h : ℤ) ≤ lim.word) :
    Meets lim program 0 d [h,dst,work] μ (time h)
      (fun r μ' => r = (localThreshold h : ℤ) ∧ Seg μ' dst (values h) ∧
        KeptBut μ μ' work dst 6) := procs.meets hw hd hout hspace hword
end ThreeSum.LightLocalCounts
