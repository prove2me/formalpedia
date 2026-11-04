-- Prove2me | solution 1 for ThreeSum.LightTernaryNearEnumerationMain.program_meets
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:55:43.632202+00:00
-- url     : https://prove2.me/submissions/9f4fc6b5-067e-4633-86cf-7fd38fddf232

import Definitions.Def_Submission_ThreeSum_LightTernaryNearEnumeration
import Definitions.Def_Submission_ThreeSum_TernaryNearBankEnumeration
import Definitions.Def_Submission_ThreeSum_LightTernaryNearEnumerationMain
import Theorems.Thm_ThreeSum_LightTernaryNearEnumerationMain_meets
import Definitions.Def_WeightedCache3SUM_Alias_098d503c7eb426c7
import Theorems.Thm_ThreeSum_LightTernaryEnumeration_meets


set_option autoImplicit false
open ThreeSum ThreeSum.LightTernaryNearEnumerationMain
open Light ThreeSum.LightSubsetAddress ThreeSum.TernaryAddresses
open ThreeSum.TernaryNearEnumeration ThreeSum.LightTernaryNearEnumeration
set_option maxHeartbeats 3000000
variable {lim : Limits} {P : Program}
namespace ThreeSum.LightTernaryNearEnumerationMain
theorem _root_.solution {W powers D pref dst caps d : ℕ} {qs : List ℕ} {μ : ℕ→ℤ}
    (hw : (lim.space : ℤ)≤lim.word)
    (hspace : powers+(2*W+1)≤lim.space)
    (hword : ((4^(W+1) : ℕ) : ℤ)≤lim.word)
    (hqs : ∀ q∈qs, q<3) (hN : qs.length≤W) (hD : D≤2*W)
    (hprefix : pref+4^qs.length≤4^W)
    (hdstP : dst+(words qs D).length≤powers)
    (hdstC : dst+(words qs D).length≤caps) (hcspace : caps+qs.length≤lim.space)
    (hpowers : Powers μ powers (2*W)) (hcaps : Seg μ caps (qs.map (fun q => (q : ℤ))))
    (hd : d+2*qs.length≤lim.depth) :
    Meets lim LightTernaryNearEnumeration.program 0 d
      [qs.length,D,pref,dst,powers,caps] μ (time qs D)
      (fun count μ' => count=((words qs D).length : ℤ) ∧
        Seg μ' dst (output qs D pref) ∧ SameOutside μ μ' dst (words qs D).length) :=
  meets rfl rfl hw hspace hword qs D pref dst caps μ
    hqs hN hD hprefix hdstP hdstC hcspace hpowers hcaps d hd
end ThreeSum.LightTernaryNearEnumerationMain
