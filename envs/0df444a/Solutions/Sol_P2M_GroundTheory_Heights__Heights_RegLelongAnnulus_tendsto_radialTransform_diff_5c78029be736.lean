-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RegLelongAnnulus_tendsto_radialTransform_diff_5c78029be736
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T08:58:18.773546+00:00
-- url     : https://prove2.me/submissions/b24c68ed-6041-4278-b57f-4ff7151183f6

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StRegRadialWeight
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StChartMassCompact
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PSheetSumMeasurable
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PFiniteProjectionCluster
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PRegLelongAnnulus
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RegLelongAnnulus_radialTransform_hk_of_le_64a107755ae3
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RegLelongAnnulus_radialTransform_hk_of_one_le_ce02361cae31
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RegLelongAnnulus_tendsto_Ik_fc9667f8e9a2
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RegLelongAnnulus_eventually_le_pk_e21fc678d92e
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RegLelongAnnulus_distSq_nonneg_983e714bd225
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RegLelongAnnulus_mem_euclBall_iff_sq_96ae1db3f54f
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RegLelongAnnulus_radialTransform_diff_of_le_d2a53db5a632
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RegLelongAnnulus_radialTransform_diff_of_ge_391b6e41a911

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
variable {r s : ℝ} (e : ℕ)
variable {n : ℕ} (x : Fin n → ℂ)
namespace GroundTheory.Heights₂.Heights.RegLelongAnnulus
theorem _root_.solution (hr : 0 < r) (hrs : r ≤ s) (z : Fin n → ℂ) :
    Tendsto (fun k => radialTransform (e + 1) (hk k) (euclPot (z - x) / s ^ 2) -
        radialTransform (e + 1) (hk k) (euclPot (z - x) / r ^ 2)) atTop
      (𝓝 ((euclBall x s \ euclBall x r).indicator (fun _ => (1 : ℝ)) z)) := by
  have hs : 0 < s := hr.trans_le hrs
  have hr2 := pow_pos hr 2
  have hs2 : r ^ 2 ≤ s ^ 2 := pow_le_pow_left₀ hr.le hrs 2
  have h0 := distSq_nonneg x z
  rcases lt_or_ge (euclPot (z - x)) (r ^ 2) with h1 | h1
  · rw [Set.indicator_of_notMem (fun h => h.2 ((mem_euclBall_iff_sq x hr z).2 h1))]
    refine tendsto_const_nhds.congr' ((eventually_le_pk ((div_lt_one hr2).2 h1)).mono fun k hk' => ?_)
    exact (radialTransform_diff_of_le e hr hrs k h0 ((div_le_iff₀ hr2).1 hk')).symm
  rcases lt_or_ge (euclPot (z - x)) (s ^ 2) with h2 | h2
  · rw [Set.indicator_of_mem (show z ∈ euclBall x s \ euclBall x r from ⟨(mem_euclBall_iff_sq x hs z).2 h2,
      fun h => (not_lt.2 h1) ((mem_euclBall_iff_sq x hr z).1 h)⟩)]
    have hv : euclPot (z - x) / s ^ 2 < 1 := (div_lt_one (hr2.trans_le hs2)).2 h2
    refine (tendsto_Ik e).congr' ((eventually_le_pk hv).mono fun k hk' => ?_)
    beta_reduce
    rw [radialTransform_hk_of_le e k (div_nonneg h0 (hr2.trans_le hs2).le) hk',
      radialTransform_hk_of_one_le e k ((one_le_div hr2).2 h1)]
    ring
  · rw [Set.indicator_of_notMem (fun h => (not_lt.2 h2) ((mem_euclBall_iff_sq x hs z).1 h.1))]
    simp only [radialTransform_diff_of_ge e hr hrs _ h2]
    exact tendsto_const_nhds
end GroundTheory.Heights₂.Heights.RegLelongAnnulus
