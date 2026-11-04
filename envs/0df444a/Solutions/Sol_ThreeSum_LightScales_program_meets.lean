-- Prove2me | solution 1 for ThreeSum.LightScales.program_meets
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:22:13.600619+00:00
-- url     : https://prove2.me/submissions/d50abe7c-b46a-49ef-bba3-55d1086211bd

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
theorem _root_.solution {μ : ℕ → ℤ} {n dst d : ℕ}
    (hw : (lim.space : ℤ) ≤ lim.word) (hspace : dst+5 ≤ lim.space)
    (hword : ((1000*(n+1) : ℕ) : ℤ) ≤ lim.word) (hd : d < lim.depth) :
    Meets lim program 0 d [n,dst] μ (time n)
      (fun r μ' => r = (mu n : ℤ) ∧ Seg μ' dst (values n) ∧ SameOutside μ μ' dst 5) :=
  meets rfl rfl rfl rfl rfl hw hspace hword hd
end ThreeSum.LightScales
