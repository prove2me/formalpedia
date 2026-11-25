-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_CellDSq_sign_swap_4c00e12af7e2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T04:45:08.450375+00:00
-- url     : https://prove2.me/submissions/c49b4caf-f88d-460f-aa3d-7b428296f956

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_ImportsBisFurther
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_DoubleSumEqZero
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_CellDSq_sign_swap_same_ecd316b75f4a
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_CellDSq_sign_swap_lt_a87248027975
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_CellDSq_rem_apply_of_ne_b09e69f4d050
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_CellDSq_rem_apply_self_da85ab734491
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_CellDSq_two_le_card_78d7df866fb8

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
theorem _root_.solution {I : ∀ k, Finset (ι k)} {p q : Σ k, ι k} (hp : p.2 ∈ I p.1) (hq : q.2 ∈ I q.1)
    (hne : q ≠ p) (hJ : ∀ l, (rem (rem I p) q l).Nonempty) :
    faceSign I p.1 p.2 * faceSign (rem I p) q.1 q.2 =
      -(faceSign I q.1 q.2 * faceSign (rem I q) p.1 p.2) := by
  obtain ⟨k, i⟩ := p
  obtain ⟨k', i'⟩ := q
  rcases lt_trichotomy k k' with h | rfl | h
  · have hb := hJ k
    rw [rem_apply_of_ne _ h.ne, rem_apply_self] at hb
    rw [sign_swap_lt i i' hp h (two_le_card hp hb), neg_neg]
  · have hii : i' ≠ i := fun e => hne (by rw [e])
    rcases lt_or_gt_of_ne hii with h | h
    · exact sign_swap_same hq h
    · rw [sign_swap_same hp h, neg_neg]
  · have hb := hJ k'
    rw [rem_apply_self, rem_apply_of_ne _ h.ne] at hb
    exact sign_swap_lt i' i hq h (two_le_card hq hb)
end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization.CellDSq
