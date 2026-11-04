-- Prove2me | solution 1 for ThreeSum.LightBandLookup.program_meets
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:27:49.243809+00:00
-- url     : https://prove2.me/submissions/021e4a0f-5714-453a-be95-798784c13f2d

import Definitions.Def_Submission_ThreeSum_BinarySearch
import Definitions.Def_Submission_ThreeSum_LightSubsetAddress
import Definitions.Def_Submission_ThreeSum_LightBandLookup
import Definitions.Def_WeightedCache3SUM_Alias_d9563e39a04084e5

set_option autoImplicit false
open ThreeSum ThreeSum.LightBandLookup
open Light ThreeSum.LightSubsetAddress
variable {lim : Limits} {P : Program}
namespace ThreeSum.LightBandLookup
theorem _root_.solution {a b n powers W L d : ℕ} {x : ℤ}
    (μ : ℕ → ℤ) (lo hi : ℕ → ℤ)
    (hw : (lim.space : ℤ) ≤ lim.word)
    (ha : a+n ≤ lim.space) (hb : b+n ≤ lim.space)
    (hspace : powers+(W+1) ≤ lim.space)
    (hword : ((n+2^(W+1)+16 : ℕ) : ℤ) ≤ lim.word)
    (hreadLo : ∀ i < n, μ (a+i) = lo i)
    (hreadHi : ∀ i < n, μ (b+i) = hi i)
    (hpowers : Powers μ powers W)
    (hsorted : ∀ i j, i ≤ j → j < n → lo i ≤ lo j)
    (hL : L ≤ W) (hn : n < 2^L) (hd : d+L+1 ≤ lim.depth) :
    Meets lim program 0 d [a,b,n,x,powers,L] μ (time L)
      (fun r μ' => r = (result lo hi n x : ℤ) ∧ μ' = μ) :=
  meets rfl rfl μ lo hi hw ha hb hspace hword hreadLo hreadHi hpowers hsorted hL hn hd
end ThreeSum.LightBandLookup
