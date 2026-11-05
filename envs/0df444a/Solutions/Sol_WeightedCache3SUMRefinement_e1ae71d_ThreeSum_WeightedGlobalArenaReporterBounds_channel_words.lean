-- Prove2me | solution 1 for WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalArenaReporterBounds.channel_words
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T12:54:27.082912+00:00
-- url     : https://prove2.me/submissions/679d0a91-6ed5-4abf-9424-e28fbf0daa8a

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_LightTernaryPostSelection
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryMomentChannelResources
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaLayout
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaReporterBounds
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalMomentChannelResources_add_word_le
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalMomentChannelResources_left_word_le
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalMomentChannelResources_right_word_le
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalMomentChannelResources_terms_word_le
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalMomentWeightBounds_left_word_bound
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalMomentWeightBounds_right_word_bound


set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalArenaReporterBounds
open Light WeightedGlobalArenaLayout LightOriginalSurvivors
open WeightedGlobalNativeMomentBounds WeightedGlobalMomentWeightBounds
namespace WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalArenaReporterBounds
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
end WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalArenaReporterBounds
