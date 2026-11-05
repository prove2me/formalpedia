-- Prove2me | solution 1 for WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightCacheEnumeration.program_meets
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T10:22:54.950209+00:00
-- url     : https://prove2.me/submissions/6d80c471-5597-483b-9c55-58cfc4981ca8

import Definitions.Def_Submission_ThreeSum_LightSubsetEnumeration
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Addresses
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_LightEnumeration
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightCacheEnumeration_meets
import Definitions.Def_WeightedCache3SUM_Alias_098d503c7eb426c7


set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightCacheEnumeration
set_option maxRecDepth 20000
set_option maxHeartbeats 8000000
open Light ThreeSum.WeightedEnumeration ThreeSum.WeightedAddresses
open ThreeSum.LightSubsetAddress
variable {lim : Limits} {P : Program}
namespace WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightCacheEnumeration
theorem _root_.solution {W powers N T pref dst d : ℕ} {μ : ℕ → ℤ}
    (hw : (lim.space : ℤ) ≤ lim.word)
    (hspace : powers+(2*W+1) ≤ lim.space)
    (hword : ((4^(W+1) : ℕ) : ℤ) ≤ lim.word)
    (hcontrol : ((2740*W+3000 : ℕ) : ℤ) ≤ lim.word)
    (hN : N ≤ W) (hT : T ≤ 2740*W) (hprefix : pref+4^N ≤ 4^W)
    (hdst : dst+(codes N T).length ≤ powers) (hpowers : Powers μ powers (2*W))
    (hd : d+N ≤ lim.depth) :
    Meets lim program 0 d [N,T,pref,dst,powers] μ (time N T)
      (fun r μ' => r = ((codes N T).length : ℤ) ∧
        Seg μ' dst (output N T pref) ∧ SameOutside μ μ' dst (codes N T).length) :=
  meets rfl hw hspace hword hcontrol N T pref dst μ hN hT hprefix hdst hpowers d hd
end WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightCacheEnumeration
