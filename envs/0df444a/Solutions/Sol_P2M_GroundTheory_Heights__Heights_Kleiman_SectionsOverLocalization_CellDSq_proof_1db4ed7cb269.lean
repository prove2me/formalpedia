-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_CellDSq_proof_1db4ed7cb269
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T07:28:23.615978+00:00
-- url     : https://prove2.me/submissions/6160312f-a4ed-4ddd-a8c5-1ba4f7c98e4f

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_ImportsBisFurther
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_DoubleSumEqZero
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_CellDSq_rem_apply_of_ne_b09e69f4d050
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_CellDSq_rem_apply_self_da85ab734491
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_CellDSq_double_sum_eq_zero_ad10d44073ea
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_CellDSq_ext_ne_zero_a50a237c8230
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_CellDSq_cellD_apply_c7b2d23830f4
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_CellDSq_cellD_apply_not_14cc3ff14943
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_CellDSq_meets_rem_3cd5209d76fc
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_CellDSq_rem_isCell_f69e623b144e
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_CellDSq_ext_of_empty_29cb4583223d

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
open CellDSq
namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
namespace CellDSq
theorem _root_.solution : CellDSq.Statement := by
  intro S _ K _ _ ι _ _ Ω _ _ y n s
  funext I
  show cellD S y (n + 1) (cellD S y n s) I = 0
  by_cases hI : CellMeets y I.1
  · rw [cellD_apply S y (n + 1) _ I hI]
    have key : ∀ k, ∀ i ∈ I.1 k, ext (n + 1) (cellD S y n s) (rem I.1 ⟨k, i⟩) =
        ∑ k', ∑ i' ∈ rem I.1 ⟨k, i⟩ k',
          faceSign (rem I.1 ⟨k, i⟩) k' i' • ext n s (rem (rem I.1 ⟨k, i⟩) ⟨k', i'⟩) := by
      intro k i hi
      by_cases hne : ((I.1 k).erase i).Nonempty
      · have hc := rem_isCell I hi hne
        rw [ext, dif_pos hc, cellD_apply S y n s ⟨_, hc⟩ (meets_rem hI _)]
      · have h0 : rem I.1 ⟨k, i⟩ k = ∅ := by
          rw [rem_apply_self]; exact Finset.not_nonempty_iff_eq_empty.1 hne
        rw [ext_of_empty _ h0]
        refine (Finset.sum_eq_zero fun k' _ => Finset.sum_eq_zero fun i' _ => ?_).symm
        rw [ext_of_empty (k := k), smul_zero]
        by_cases hk : k = k'
        · subst hk; rw [rem_apply_self, h0, Finset.erase_empty]
        · rw [rem_apply_of_ne _ hk, h0]
    rw [Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i hi => by rw [key k i hi]]
    exact double_sum_eq_zero I.1 (ext n s) (ext_ne_zero s)
  · exact cellD_apply_not S y (n + 1) _ I hI
end CellDSq
end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
