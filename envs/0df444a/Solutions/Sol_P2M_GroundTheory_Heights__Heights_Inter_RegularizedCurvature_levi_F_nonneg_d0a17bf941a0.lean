-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_RegularizedCurvature_levi_F_nonneg_d0a17bf941a0
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:23:36.354728+00:00
-- url     : https://prove2.me/submissions/b022415a-7b4c-4d4f-9113-192e25cbbdcf

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_ADensStC
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_PshShiftA
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_LeviOneEqLaplacianThm
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_ArithModel
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_RegularizedCurvature
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_RegularizedCurvature_blk_ne_5d655089f8c5
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_ProjLine_isSmoothMetric_fs_21e0570fe462
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_ProjLine_leviForm_log_fs_nonneg_4c974b17d733
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_adens_contDiffAt_log__id_ce5e717798ac
import Theorems.Thm_ReciprocityTheory_AnForm_levi_comp


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
open GroundTheory.Heights₂.Heights.Inter.RegularizedCurvature
open ReciprocityTheory.ChartRestriction.G.Geo Filter Topology InnerProductSpace Laplacian
set_option linter.unusedSectionVars false
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
namespace GroundTheory.Heights₂.Heights.Inter.RegularizedCurvature
theorem _root_.solution {z : (Σ k, ι k) → ℂ} (hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) (k : K)
    (w : (Σ k, ι k) → ℂ) : 0 ≤ ReciprocityTheory.AnForm.levi (F k) z w := by
  have hφ := ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.adens_contDiffAt_logρ_id
    (GroundTheory.Heights₂.Heights.HilbertSamuel.ProjLine.isSmoothMetric_fs (J := ι k)) (blk_ne hz k)
  have hFk : F k = (fun u => Real.log ((fsMetric (ι k)).ρ u)) ∘ blk (ι := ι) k := rfl
  rw [hFk, ReciprocityTheory.AnForm.levi_comp w ((blk (ι := ι) k).analyticAt z) hφ]
  exact GroundTheory.Heights₂.Heights.HilbertSamuel.ProjLine.leviForm_log_fs_nonneg (blk_ne hz k) _
end GroundTheory.Heights₂.Heights.Inter.RegularizedCurvature
