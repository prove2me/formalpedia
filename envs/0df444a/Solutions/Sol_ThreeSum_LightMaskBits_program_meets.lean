-- Prove2me | solution 1 for ThreeSum.LightMaskBits.program_meets
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:41:18.137191+00:00
-- url     : https://prove2.me/submissions/5a1d669c-ecf1-42d7-97b0-30e5bfa05cf4

import Definitions.Def_Submission_ThreeSum_LightMaskErase
import Definitions.Def_Submission_ThreeSum_MaskDecode
import Definitions.Def_Submission_ThreeSum_LightMaskBits
import Definitions.Def_WeightedCache3SUM_Alias_737c7144994f79de
import Definitions.Def_WeightedCache3SUM_Alias_de0ba8c01a8a208c


set_option autoImplicit false
open ThreeSum ThreeSum.LightMaskBits
open Light LightSubsetAddress MaskErase
variable {lim : Limits} {P : Program} {d : ℕ}
namespace ThreeSum.LightMaskBits
theorem _root_.solution
    {μ : ℕ → ℤ} {L m dst work : ℕ}
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : d+L+1 ≤ lim.depth)
    (hspace : work+(L+1) ≤ lim.space) (hdst : dst+L ≤ work)
    (hword : ((2^(L+1) : ℕ) : ℤ) ≤ lim.word) (hm : m < 2^L) :
    Meets lim program 0 d [L,m,dst,work] μ (time L)
      (fun _ μ' => (∀ j < L, μ' (dst+j) = (bit L m j : ℤ)) ∧
        Powers μ' work L ∧ KeptBut μ μ' work dst L) :=
  meets rfl rfl rfl hw hd hspace hdst hword hm
end ThreeSum.LightMaskBits
