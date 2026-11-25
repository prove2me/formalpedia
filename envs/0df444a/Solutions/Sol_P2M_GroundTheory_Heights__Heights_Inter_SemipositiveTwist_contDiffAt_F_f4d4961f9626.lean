-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_SemipositiveTwist_contDiffAt_F_f4d4961f9626
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T05:53:32.927208+00:00
-- url     : https://prove2.me/submissions/8685c8bf-13c2-4d75-b413-bf8d47e8f359

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_NoCommonComponentCoordinatesPlane
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StTorusInvLevi
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_ArithModel
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_ADensStC
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_PshShiftA
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_LeviOneEqLaplacianThm
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PSemiPosTwist
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_SemipositiveTwist_blk_ne_ce9f3419af7a
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_ProjLine_isSmoothMetric_fs_21e0570fe462
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_adens_contDiffAt_log__id_ce5e717798ac


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open ReciprocityTheory.ChartRestriction.G.Geo Filter Topology InnerProductSpace Laplacian
open GroundTheory.Heights₂.Heights.Inter.SemipositiveTwist
set_option linter.unusedSectionVars false
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
namespace GroundTheory.Heights₂.Heights.Inter.SemipositiveTwist
theorem _root_.solution {z : (Σ k, ι k) → ℂ} (hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) (k : K) :
    ContDiffAt ℝ 2 (F k) z := by
  have hφ := ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.adens_contDiffAt_logρ_id
    (GroundTheory.Heights₂.Heights.HilbertSamuel.ProjLine.isSmoothMetric_fs (J := ι k)) (blk_ne hz k)
  have hFk : F k = (fun u => Real.log ((fsMetric (ι k)).ρ u)) ∘ blk (ι := ι) k := rfl
  rw [hFk]
  exact hφ.comp z ((blk (ι := ι) k).restrictScalars ℝ).contDiff.contDiffAt
end GroundTheory.Heights₂.Heights.Inter.SemipositiveTwist
