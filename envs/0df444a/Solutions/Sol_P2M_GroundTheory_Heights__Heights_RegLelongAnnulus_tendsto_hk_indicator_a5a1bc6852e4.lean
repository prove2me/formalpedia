-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RegLelongAnnulus_tendsto_hk_indicator_a5a1bc6852e4
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T07:15:51.097795+00:00
-- url     : https://prove2.me/submissions/8ee363ee-6711-45bc-9fb6-57e20739cf58

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StRegRadialWeight
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StChartMassCompact
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PSheetSumMeasurable
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PFiniteProjectionCluster
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PRegLelongAnnulus
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RegLelongAnnulus_hk_one_b52240beee02
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RegLelongAnnulus_hk_zero_of_one_le_400cd7c12e4c
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RegLelongAnnulus_eventually_le_pk_e21fc678d92e
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RegLelongAnnulus_distSq_nonneg_983e714bd225
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RegLelongAnnulus_mem_euclBall_iff_sq_96ae1db3f54f

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets
open scoped ContDiff
noncomputable section
open GroundTheory.Heights₂.Heights.RegLelongAnnulus
variable {n : ℕ} (x : Fin n → ℂ)
namespace GroundTheory.Heights₂.Heights.RegLelongAnnulus
theorem _root_.solution {ρ : ℝ} (hρ : 0 < ρ) (z : Fin n → ℂ) :
    Tendsto (fun k => hk k (euclPot (z - x) / ρ ^ 2)) atTop
      (𝓝 ((euclBall x ρ).indicator (fun _ => (1 : ℝ)) z)) := by
  have hρ2 := pow_pos hρ 2
  have hv0 : 0 ≤ euclPot (z - x) / ρ ^ 2 := div_nonneg (distSq_nonneg x z) hρ2.le
  by_cases hz : euclPot (z - x) < ρ ^ 2
  · rw [Set.indicator_of_mem ((mem_euclBall_iff_sq x hρ z).2 hz)]
    have hv : euclPot (z - x) / ρ ^ 2 < 1 := (div_lt_one hρ2).2 hz
    exact tendsto_const_nhds.congr' ((eventually_le_pk hv).mono fun k hk' => (hk_one hv0 hk').symm)
  · rw [Set.indicator_of_notMem (fun h => hz ((mem_euclBall_iff_sq x hρ z).1 h))]
    have hv : 1 ≤ euclPot (z - x) / ρ ^ 2 := (one_le_div hρ2).2 (not_lt.1 hz)
    simp only [hk_zero_of_one_le hv]
    exact tendsto_const_nhds
end GroundTheory.Heights₂.Heights.RegLelongAnnulus
