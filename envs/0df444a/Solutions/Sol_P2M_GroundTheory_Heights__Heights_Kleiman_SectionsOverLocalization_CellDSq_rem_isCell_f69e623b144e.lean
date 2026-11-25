-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_CellDSq_rem_isCell_f69e623b144e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T03:29:20.728155+00:00
-- url     : https://prove2.me/submissions/7a57527c-4bc7-4a97-ba3e-f463addf84a6

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_ImportsBisFurther
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_DoubleSumEqZero
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
variable (S : Type) [CommRing S] [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω] [Algebra S Ω]
omit [∀ k, Fintype (ι k)] [Algebra S Ω]
namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization.CellDSq
theorem _root_.solution {m : ℕ} (J : Cell K ι (m + 1)) {k : K} {i : ι k} (hi : i ∈ J.1 k)
    (hne : ((J.1 k).erase i).Nonempty) :
    (∀ l, (rem J.1 ⟨k, i⟩ l).Nonempty) ∧ ∑ l, ((rem J.1 ⟨k, i⟩ l).card - 1) = m := by
  have hdeg := J.2.2
  have hk := two_le_card hi hne
  refine ⟨fun l => ?_, ?_⟩
  · by_cases hl : l = k
    · subst hl; rw [rem_apply_self]; exact hne
    · rw [rem_apply_of_ne _ hl]; exact J.2.1 l
  · rw [← Finset.add_sum_erase _ _ (Finset.mem_univ k)] at hdeg ⊢
    rw [rem_apply_self, Finset.card_erase_of_mem hi,
      Finset.sum_congr rfl fun l hl => by rw [rem_apply_of_ne _ (Finset.ne_of_mem_erase hl)]]
    omega
end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization.CellDSq
