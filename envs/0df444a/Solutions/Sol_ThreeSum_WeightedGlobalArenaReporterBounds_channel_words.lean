-- Prove2me | solution 1 for ThreeSum.WeightedGlobalArenaReporterBounds.channel_words
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T16:26:40.720398+00:00
-- url     : https://prove2.me/submissions/70692bfe-de25-4fb1-a0f1-19b6850417f1

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_LightTernaryPostSelection
import Definitions.Def_Submission_Weighted_Global_TernaryMomentChannelResources
import Definitions.Def_Submission_Weighted_Global_TernaryArenaLayout
import Definitions.Def_Submission_Weighted_Global_TernaryArenaReporterBounds
import Theorems.Thm_ThreeSum_WeightedGlobalMomentChannelResources_add_word_le
import Theorems.Thm_ThreeSum_WeightedGlobalMomentChannelResources_left_word_le
import Theorems.Thm_ThreeSum_WeightedGlobalMomentChannelResources_right_word_le
import Theorems.Thm_ThreeSum_WeightedGlobalMomentChannelResources_terms_word_le
import Theorems.Thm_ThreeSum_WeightedGlobalMomentWeightBounds_left_word_bound
import Theorems.Thm_ThreeSum_WeightedGlobalMomentWeightBounds_right_word_bound


set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalArenaReporterBounds
open Light WeightedGlobalArenaLayout LightOriginalSurvivors
open WeightedGlobalNativeMomentBounds WeightedGlobalMomentWeightBounds
namespace ThreeSum.WeightedGlobalArenaReporterBounds
theorem _root_.solution (lim : Limits) (pairMass U K : ℕ)
    (hw : ((WeightedGlobalMomentChannelResources.need pairMass U K).word : ℤ)≤lim.word) :
    (∀ k<K+1, ∀ j≤k,
      max (U : ℤ) (2*((k.choose j : ℤ)+1)*((U : ℤ)+2)^j)≤lim.word) ∧
    (∀ k<K+1, ∀ j≤k,
      max (U : ℤ) (2*((U : ℤ)+1)^(k-j))≤lim.word) ∧
    2*(((TernaryMomentSchedule.channels (K+1)).length*
      WeightedGlobalMomentChannelResources.scoreBound pairMass U K : ℕ) : ℤ)≤lim.word ∧
    (K+1 : ℕ)≤lim.word := by
  refine ⟨?_,?_,?_,?_⟩
  · intro k hk j hj
    exact (left_word_bound (by omega) hj).trans
      ((Int.ofNat_le.mpr (WeightedGlobalMomentChannelResources.left_word_le pairMass U K)).trans hw)
  · intro k hk j hj
    exact (right_word_bound (by omega)).trans
      ((Int.ofNat_le.mpr (WeightedGlobalMomentChannelResources.right_word_le pairMass U K)).trans hw)
  · have ha : 2*(((TernaryMomentSchedule.channels (K+1)).length*
        WeightedGlobalMomentChannelResources.scoreBound pairMass U K : ℕ) : ℤ)≤
        ((WeightedGlobalMomentChannelResources.need pairMass U K).word : ℤ) := by
      exact_mod_cast WeightedGlobalMomentChannelResources.add_word_le pairMass U K
    exact ha.trans hw
  · exact (Int.ofNat_le.mpr (WeightedGlobalMomentChannelResources.terms_word_le pairMass U K)).trans hw
end ThreeSum.WeightedGlobalArenaReporterBounds
