-- Prove2me | solution 1 for ThreeSum.LightTernaryCarryCodes.program_meets
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:45:39.208144+00:00
-- url     : https://prove2.me/submissions/4c750633-368d-4d52-b6ba-b72f53935e28

import Definitions.Def_Submission_ThreeSum_LightOutputDecodeDigits
import Definitions.Def_Submission_ThreeSum_TernaryCarryCode
import Definitions.Def_Submission_ThreeSum_LightNatPower
import Definitions.Def_Submission_ThreeSum_LightTernaryCarryCodes
import Theorems.Thm_ThreeSum_LightTernaryCarryCodes_meets
import Definitions.Def_WeightedCache3SUM_Alias_d7235e9f603abd3f
import Definitions.Def_WeightedCache3SUM_Alias_737c7144994f79de
import Definitions.Def_WeightedCache3SUM_Alias_de0ba8c01a8a208c
import Definitions.Def_WeightedCache3SUM_Alias_d92129e9a4741fac
import Definitions.Def_WeightedCache3SUM_Alias_54f2bf19dfb01d66
import Definitions.Def_WeightedCache3SUM_Alias_9a4576158068ee52


set_option autoImplicit false
open ThreeSum ThreeSum.LightTernaryCarryCodes
open Light TernarySignedDigits
set_option maxHeartbeats 2400000
set_option maxRecDepth 9000
variable {lim : Limits} {P : Program} {d : ℕ} {μ : ℕ → ℤ}
namespace ThreeSum.LightTernaryCarryCodes
theorem _root_.solution {J dst work : ℕ}
    (hw : (lim.space : ℤ)≤lim.word) (hd : d+4<lim.depth)
    (hsep : dst+2^J*(J+1)≤work)
    (hspace : space work (2^J)≤lim.space)
    (hword : (word J (2^J) : ℤ)≤lim.word) :
    Meets lim program 0 d [J,dst,work] μ (time J)
      (fun r ν => r=(2^J : ℕ) ∧ Table ν dst J (2^J) ∧ Kept μ ν dst) :=
  meets rfl rfl rfl rfl rfl rfl hw hd hsep hspace hword
end ThreeSum.LightTernaryCarryCodes
