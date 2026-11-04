-- Prove2me | solution 1 for ThreeSum.LightParameterInit.program_meets
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T12:31:18.362837+00:00
-- url     : https://prove2.me/submissions/59805c3d-ab9c-4542-83c3-c8064d014fb0

import Definitions.Def_Submission_ThreeSum_LightScales
import Definitions.Def_Submission_ThreeSum_LightLocalParameters
import Definitions.Def_Submission_ThreeSum_LightGlobalSizes
import Definitions.Def_Submission_ThreeSum_LightParameterInit
import Definitions.Def_WeightedCache3SUM_Alias_97fa2774a4e14663
import Definitions.Def_WeightedCache3SUM_Alias_3718d050d478b160
import Definitions.Def_WeightedCache3SUM_Alias_9f151fd16c06b1ef
import Definitions.Def_WeightedCache3SUM_Alias_e2ad5e59f3af6ab7
import Definitions.Def_WeightedCache3SUM_Alias_d92129e9a4741fac
import Theorems.Thm_ThreeSum_LightPrimality_Procs_meets
import Definitions.Def_WeightedCache3SUM_Alias_137b880911028d95
import Definitions.Def_WeightedCache3SUM_Alias_a00dee90c4e0ea45
import Definitions.Def_WeightedCache3SUM_Alias_9b3006da0fcbdf4e
import Theorems.Thm_ThreeSum_LightScales_Procs_meets
import Definitions.Def_WeightedCache3SUM_Alias_984013d7ba738e5d
import Definitions.Def_WeightedCache3SUM_Alias_276ab4baf5d9c1f3
import Definitions.Def_WeightedCache3SUM_Alias_73246870e6a638ab
import Definitions.Def_WeightedCache3SUM_Alias_8a94481881de516b


set_option autoImplicit false
open ThreeSum ThreeSum.LightParameterInit
open Light LocalCoverBounds Scales
set_option maxHeartbeats 1500000
set_option maxRecDepth 5000
variable {lim : Limits} {P : Program} {d : ℕ}
namespace ThreeSum.LightParameterInit
theorem _root_.solution {μ : ℕ → ℤ} {n dst work : ℕ}
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : d+512*half n+6 ≤ lim.depth)
    (hout : dst+19 ≤ work) (hspace : space work n ≤ lim.space)
    (hword : (word n : ℤ) ≤ lim.word) :
    Meets lim program 0 d [n,dst,work] μ (time n)
      (fun r μ' => r = (radix n : ℤ) ∧ Seg μ' dst (values n) ∧
        KeptBut μ μ' work dst 19) := procs.meets hw hd hout hspace hword
end ThreeSum.LightParameterInit
