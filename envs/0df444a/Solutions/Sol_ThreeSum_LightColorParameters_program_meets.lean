-- Prove2me | solution 1 for ThreeSum.LightColorParameters.program_meets
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:50:52.185749+00:00
-- url     : https://prove2.me/submissions/355714cd-a4b9-428e-add4-5ec2fe70d23b

import Definitions.Def_Submission_ThreeSum_ColorParameters
import Definitions.Def_Submission_ThreeSum_LightSmallDivide
import Definitions.Def_Submission_ThreeSum_LightArray
import Mathlib.Tactic.IntervalCases
import Definitions.Def_Submission_ThreeSum_LightColorParameters
import Definitions.Def_WeightedCache3SUM_Alias_6cd6f72823a59258
import Definitions.Def_WeightedCache3SUM_Alias_98152438e5b788f3
import Definitions.Def_WeightedCache3SUM_Alias_5d83a00a3f301eb9
import Definitions.Def_WeightedCache3SUM_Alias_de0ba8c01a8a208c
import Definitions.Def_WeightedCache3SUM_Alias_73246870e6a638ab


set_option autoImplicit false
open ThreeSum ThreeSum.LightColorParameters
open Light ColorParameters
set_option maxHeartbeats 1600000
set_option maxRecDepth 9000
variable {lim : Limits} {P : Program} {d W t free : ℕ} {μ : ℕ → ℤ}
namespace ThreeSum.LightColorParameters
theorem _root_.solution (hw : (lim.space : ℤ) ≤ lim.word) (hspace : free+6 ≤ lim.space)
    (hword : ((t+W+10 : ℕ) : ℤ) ≤ lim.word) (hd : d < lim.depth) :
    Meets lim program 0 d [W,t,free] μ (time t)
      (fun result ν => result=(free : ℤ) ∧ Seg ν free (data W t) ∧ SameOutside μ ν free 6) :=
  meets rfl rfl hw hspace hword hd
end ThreeSum.LightColorParameters
