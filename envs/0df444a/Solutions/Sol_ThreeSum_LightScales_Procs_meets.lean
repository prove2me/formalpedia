-- Prove2me | solution 1 for ThreeSum.LightScales.Procs.meets
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:25:21.21388+00:00
-- url     : https://prove2.me/submissions/98a17208-10b1-4b65-970f-2121e0f9e4ae

import Definitions.Def_Submission_ThreeSum_Scales
import Definitions.Def_Submission_ThreeSum_LightSmallDivide
import Definitions.Def_Submission_ThreeSumApsp_Lang_Lib_Seg
import Definitions.Def_Submission_ThreeSum_LightScales
import Definitions.Def_WeightedCache3SUM_Alias_984013d7ba738e5d
import Definitions.Def_WeightedCache3SUM_Alias_73246870e6a638ab


set_option autoImplicit false
open ThreeSum ThreeSum.LightScales
open Light ThreeSum.Scales
variable {lim : Limits} {P : Program}
namespace ThreeSum.LightScales
namespace Procs
theorem _root_.solution {pMain : ℕ} (S : Procs P pMain)
    {μ : ℕ → ℤ} {n dst d : ℕ}
    (hw : (lim.space : ℤ) ≤ lim.word) (hspace : dst+5 ≤ lim.space)
    (hword : ((1000*(n+1) : ℕ) : ℤ) ≤ lim.word) (hd : d < lim.depth) :
    Meets lim P pMain d [n,dst] μ (time n)
      (fun r μ' => r = (mu n : ℤ) ∧ Seg μ' dst (values n) ∧ SameOutside μ μ' dst 5) :=
  LightScales.meets S.main S.log S.cube S.half S.divide hw hspace hword hd
end Procs
end ThreeSum.LightScales
