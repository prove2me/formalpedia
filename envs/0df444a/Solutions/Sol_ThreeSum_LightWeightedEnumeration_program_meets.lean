-- Prove2me | solution 1 for ThreeSum.LightWeightedEnumeration.program_meets
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:41:25.149533+00:00
-- url     : https://prove2.me/submissions/42766450-cb85-4043-a022-47f2bca3a59f

import Definitions.Def_Submission_ThreeSum_LightSubsetEnumeration
import Definitions.Def_Submission_ThreeSum_LightWeightedEnumeration
import Definitions.Def_WeightedCache3SUM_Alias_faf0bf412734022a
import Definitions.Def_WeightedCache3SUM_Alias_098d503c7eb426c7
import Theorems.Thm_ThreeSum_LightSubsetEnumeration_work_pos


set_option autoImplicit false
open ThreeSum ThreeSum.LightWeightedEnumeration
open Light ThreeSum.SubsetAddress ThreeSum.LightSubsetAddress
open LightSubsetEnumeration (time work_pos)
open scoped BigOperators
variable {lim : Limits} {P : Program}
namespace ThreeSum.LightWeightedEnumeration
theorem _root_.solution {W powers U L k pref dst d : ℕ} {weights : ℕ → ℕ} {μ : ℕ → ℤ}
    (hw : (lim.space : ℤ) ≤ lim.word)
    (hspace : powers+(W+1) ≤ lim.space)
    (hword : (U : ℤ) ≤ lim.word)
    (hL : L ≤ W) (hk : k ≤ W+1) (hprefix : pref+total weights L ≤ U)
    (hdst : dst+L.choose k ≤ powers) (hpowers : Weights μ powers W weights)
    (hd : d+L ≤ lim.depth) :
    Meets lim program 0 d [L,k,pref,dst,powers] μ (time L k)
      (fun r μ' => r = (L.choose k : ℤ) ∧
        Seg μ' dst (output weights L k pref) ∧ SameOutside μ μ' dst (L.choose k)) :=
  meets rfl hw hspace hword L k pref dst μ hL hk hprefix hdst hpowers d hd
end ThreeSum.LightWeightedEnumeration
