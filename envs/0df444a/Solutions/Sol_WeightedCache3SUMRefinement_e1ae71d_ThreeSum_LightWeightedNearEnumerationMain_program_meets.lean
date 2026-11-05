-- Prove2me | solution 1 for WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedNearEnumerationMain.program_meets
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T10:24:22.831503+00:00
-- url     : https://prove2.me/submissions/b13b3db9-1c04-4124-a94c-6fdf17ceb5b2

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_LightNearEnumeration
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_LightNearEnumerationMain
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightWeightedNearEnumerationMain_meets
import Definitions.Def_WeightedCache3SUM_Alias_098d503c7eb426c7
import Theorems.Thm_ThreeSum_LightTernaryEnumeration_meets


set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedNearEnumerationMain
open Light ThreeSum.LightSubsetAddress ThreeSum.WeightedAddresses
open ThreeSum.WeightedEnumeration (digitCost)
open ThreeSum.WeightedEnumeration (digitCost)
open ThreeSum.WeightedNearEnumeration ThreeSum.LightWeightedNearEnumeration
set_option maxHeartbeats 8000000
set_option maxRecDepth 24000
variable {lim : Limits} {P : Program}
namespace WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedNearEnumerationMain
theorem _root_.solution {W powers D pref dst caps d : ℕ} {qs : List ℕ} {μ : ℕ→ℤ}
    (hw : (lim.space : ℤ)≤lim.word)
    (hspace : powers+(2*W+1)≤lim.space)
    (hword : ((4^(W+1) : ℕ) : ℤ)≤lim.word)
    (hcontrol : ((2740*W+3000 : ℕ) : ℤ)≤lim.word)
    (hqs : ∀ q∈qs, q<3) (hN : qs.length≤W) (hD : D≤2740*W)
    (hprefix : pref+4^qs.length≤4^W)
    (hdstP : dst+(words qs D).length≤powers)
    (hdstC : dst+(words qs D).length≤caps) (hcspace : caps+qs.length≤lim.space)
    (hpowers : Powers μ powers (2*W)) (hcaps : Seg μ caps (qs.map (fun q => (digitCost q : ℤ))))
    (hd : d+2*qs.length≤lim.depth) :
    Meets lim LightWeightedNearEnumeration.program 0 d
      [qs.length,D,pref,dst,powers,caps] μ (time qs D)
      (fun count μ' => count=((words qs D).length : ℤ) ∧
        Seg μ' dst (output qs D pref) ∧ SameOutside μ μ' dst (words qs D).length) :=
  meets rfl rfl hw hspace hword hcontrol qs D pref dst caps μ
    hqs hN hD hprefix hdstP hdstC hcspace hpowers hcaps d hd
end WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedNearEnumerationMain
