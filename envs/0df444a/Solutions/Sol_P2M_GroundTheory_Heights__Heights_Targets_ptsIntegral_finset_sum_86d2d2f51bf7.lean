-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Targets_ptsIntegral_finset_sum_86d2d2f51bf7
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T14:08:15.387892+00:00
-- url     : https://prove2.me/submissions/8d68a9ef-f812-422c-b6af-dc77d8b8ed55

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterFib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterDivSupp
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PPtsAddFirst
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PDeLeSemiPos
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PRFormula
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PSegrePartition
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_LogRegLineTensor
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_LelongSectionLimit
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_LelongChartLimit
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PLelongSectionLimit
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_sheetDensity_finset_sum_d5cf2f6d1e1f
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_integrable_fibreSum_degZero_510e47a67880
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_fibreFinite


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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Targets
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology MeasureTheory
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
namespace GroundTheory.Heights₂.Heights.Targets
theorem _root_.solution (hInt : PtsIntegrableStatement) {Q : Ideal (MRing ι)} {e : ℕ}
    (hQ : IsArithVar Q (e + 1)) {L : Fin e → HermLine ι} (hL : ∀ j, IsSmoothHerm (L j)) {T : Type*}
    (S : Finset T) {u : T → ((Σ k, ι k) → ℂ) → ℝ} (hu : ∀ t, IsDegZeroSmooth (u t)) :
    ptsIntegral Q (pot L) (fun z => ∑ t ∈ S, u t z) = ∑ t ∈ S, ptsIntegral Q (pot L) (u t) := by
  classical
  by_cases hΨ : ∃ Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ), IsGoodProj Q Ψ
  · simp only [ptsIntegral, dif_pos hΨ, ptsIntegralAt]
    rw [← integral_finsetSum S fun t _ =>
      integrable_fibreSum_degZero hInt hQ hΨ.choose_spec hL (hu t)]
    congr 1
    funext y
    have hfin := fibreFinite K ι Q e hΨ.choose hQ hΨ.choose_spec y
    simp only [sheetDensity_finset_sum]
    rw [finsum_mem_eq_finite_toFinset_sum _ hfin, Finset.sum_comm]
    exact Finset.sum_congr rfl fun t _ => (finsum_mem_eq_finite_toFinset_sum _ hfin).symm
  · simp [ptsIntegral, dif_neg hΨ]
end GroundTheory.Heights₂.Heights.Targets
