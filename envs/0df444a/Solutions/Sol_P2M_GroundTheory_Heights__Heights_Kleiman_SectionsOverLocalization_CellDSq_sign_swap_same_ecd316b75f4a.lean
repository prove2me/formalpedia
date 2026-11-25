-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_CellDSq_sign_swap_same_ecd316b75f4a
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T04:07:15.290388+00:00
-- url     : https://prove2.me/submissions/ad616db4-4098-466d-a84c-d14ec9e2ed11

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_ImportsBisFurther
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_DoubleSumEqZero
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_CellDSq_offset_update_2ba4b02ed54e

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
noncomputable section
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH
open GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization.CellDSq
variable {K : Type} [Fintype K] [LinearOrder K] {ι : K → Type} [∀ k, LinearOrder (ι k)]
namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization.CellDSq
theorem _root_.solution {I : ∀ k, Finset (ι k)} {k : K} {i i' : ι k} (hi : i ∈ I k) (hlt : i < i') :
    faceSign I k i' * faceSign (rem I ⟨k, i'⟩) k i = -(faceSign I k i * faceSign (rem I ⟨k, i⟩) k i') := by
  have h1 : ((I k).erase i').filter (· < i) = (I k).filter (· < i) := by
    ext z
    simp only [Finset.mem_filter, Finset.mem_erase]
    constructor
    · rintro ⟨⟨-, hz⟩, hzi⟩; exact ⟨hz, hzi⟩
    · rintro ⟨hz, hzi⟩; exact ⟨⟨(hzi.trans hlt).ne, hz⟩, hzi⟩
  have h3 : i ∈ (I k).filter (· < i') := Finset.mem_filter.2 ⟨hi, hlt⟩
  have h2 : (((I k).erase i).filter (· < i')).card + 1 = ((I k).filter (· < i')).card := by
    rw [Finset.filter_erase, Finset.card_erase_add_one h3]
  unfold faceSign rem
  simp only [Function.update_self, offset_update]
  rw [h1, ← h2]
  ring
end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization.CellDSq
