-- Prove2me | solution 1 for ThreeSum.LightMaskErase.program_meets
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:21:28.934853+00:00
-- url     : https://prove2.me/submissions/93806712-9b71-4dec-b279-b20d5b34cd97

import Definitions.Def_Submission_ThreeSum_MaskErase
import Definitions.Def_Submission_ThreeSum_LightSubsetAddress
import Definitions.Def_Submission_ThreeSum_LightMaskErase
import Definitions.Def_WeightedCache3SUM_Alias_de0ba8c01a8a208c

set_option autoImplicit false
open ThreeSum ThreeSum.LightMaskErase
open Light ThreeSum.MaskErase ThreeSum.LightSubsetAddress
variable {lim : Limits} {P : Program}
namespace ThreeSum.LightMaskErase
theorem _root_.solution {μ : ℕ → ℤ} {L a m W powers d : ℕ}
    (hw : (lim.space : ℤ) ≤ lim.word) (hspace : powers+(W+1) ≤ lim.space)
    (hword : ((2^(W+1) : ℕ) : ℤ) ≤ lim.word) (hpowers : Powers μ powers W)
    (hL : L ≤ W) (ha : a ≤ W) (hm : m < 2^L) (hd : d+L ≤ lim.depth) :
    Meets lim program 0 d [L,a,m,W,powers] μ (time L)
      (fun r μ' => r = (eraseMask L a m : ℤ) ∧ μ' = μ) :=
  meets rfl μ hw hspace hword hpowers L a m hL ha hm d hd
end ThreeSum.LightMaskErase
