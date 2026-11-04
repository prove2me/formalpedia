-- Prove2me | solution 1 for ThreeSum.LightTernaryLookup.code_meets
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:20:41.516496+00:00
-- url     : https://prove2.me/submissions/8376f858-e6fb-4ebe-9513-a92eae203746

import Definitions.Def_Submission_ThreeSum_LightBandLookup
import Definitions.Def_Submission_ThreeSum_LightTernaryCell
import Definitions.Def_Submission_ThreeSum_LightTernaryLookup
import Theorems.Thm_ThreeSum_LightTernaryLookup_code_partition
import Definitions.Def_WeightedCache3SUM_Alias_b3ed31058dd4b298


set_option autoImplicit false
open ThreeSum ThreeSum.LightTernaryLookup
open Light ThreeSum.LightSubsetAddress
variable {lim : Limits} {P : Program}
namespace ThreeSum.LightTernaryLookup
theorem _root_.solution {pSearch a n powers W L j d : ℕ}
    (hprog : P[pSearch]? = some (LightBandLookup.searchBody pSearch))
    (μ : ℕ → ℤ) (f : ℕ → ℤ)
    (hw : (lim.space : ℤ) ≤ lim.word)
    (ha : a+n ≤ lim.space) (hspace : powers+(W+1) ≤ lim.space)
    (hword : ((n+2^(W+1)+16 : ℕ) : ℤ) ≤ lim.word)
    (hread : ∀ i < n, μ (a+i) = f i)
    (hpowers : Powers μ powers W)
    (hsorted : ∀ i k, i < k → k < n → f i < f k)
    (hj : j < n) (hL : L ≤ W) (hn : n < 2^L) (hd : d+L ≤ lim.depth) :
    Meets lim P pSearch d [a,n,f j,powers,L,0] μ (LightBandLookup.searchTime L)
      (fun r μ' => r = ((j+1 : ℕ) : ℤ) ∧ μ' = μ) :=
  LightBandLookup.search_meets hprog μ f (j+1) hw ha hspace hword hread hpowers
    (code_partition f hj hsorted) L 0 hL (by omega) (by omega) d hd
end ThreeSum.LightTernaryLookup
