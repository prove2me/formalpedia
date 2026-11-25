-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AR.Up.DivLA.taylor_step
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:36:34.899206+00:00
-- url     : https://prove2.me/submissions/86aee2b6-901d-403b-9a9f-39e433d4d025

import Definitions.Def_ReciprocityTheory_AnalyticForms_AnalyticCharts_Osgood
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_IsLocalHomeomorph
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_NormFibrations_MvBlowup
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_LintegralBallRpowLtTop
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_DivStatementPfLA
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_DivLA_isBigO_norm_pow_of_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Up.DivLA
open ReciprocityTheory.L2DbarEstimates MeasureTheory Topology Filter Asymptotics
noncomputable section
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.DivLA
theorem _root_.solution {n d : ℕ} {G : V n → ℂ} (hG : AnalyticAt ℂ G 0)
    (hO : G =O[𝓝 0] fun z => ‖z‖ ^ d) :
    ∃ q : ContinuousMultilinearMap ℂ (fun _ : Fin d => V n) ℂ,
      (fun z => G z - q (fun _ => z)) =O[𝓝 0] fun z => ‖z‖ ^ (d + 1) := by
  obtain ⟨p, hp⟩ := hG
  have hvan : ∀ m, m < d → ∀ y : V n, p m (fun _ => y) = 0 := by
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ih =>
      intro hm y0
      have hps : ∀ y : V n, p.partialSum (m + 1) y = p m (fun _ => y) := by
        intro y
        simp only [FormalMultilinearSeries.partialSum, Finset.sum_range_succ]
        rw [Finset.sum_eq_zero (fun j hj => ih j (Finset.mem_range.mp hj)
          (by have := Finset.mem_range.mp hj; omega) y), zero_add]
      have hA := hp.isBigO_sub_partialSum_pow (m + 1)
      simp only [zero_add, hps] at hA
      have hB : G =O[𝓝 0] fun z => ‖z‖ ^ (m + 1) := hO.trans (isBigO_norm_pow_of_le (by omega))
      have h : (fun y : V n => p m (fun _ => y)) =O[𝓝 0] fun y => ‖y‖ ^ (m + 1) :=
        (hB.sub hA).congr_left (fun y => by ring)
      have htend : Tendsto (fun t : ℂ => t • y0) (𝓝 0) (𝓝 0) := by
        have hc : Continuous fun t : ℂ => t • y0 := continuous_id.smul continuous_const
        have := hc.tendsto 0
        simpa using this
      have h2 := h.comp_tendsto htend
      obtain ⟨C, hC⟩ := h2.bound
      have hhom : ∀ t : ℂ, p m (fun _ => t • y0) = t ^ m * p m (fun _ => y0) := by
        intro t
        have := (p m).map_smul_univ (fun _ => t) (fun _ => y0)
        rw [this, Finset.prod_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
      have hbd : ∀ᶠ t in 𝓝[≠] (0 : ℂ), ‖p m (fun _ => y0)‖ ≤ C * ‖y0‖ ^ (m + 1) * ‖t‖ := by
        filter_upwards [nhdsWithin_le_nhds hC, self_mem_nhdsWithin] with t ht ht0
        simp only [Function.comp_apply, hhom, norm_mul, norm_pow, norm_smul, mul_pow, norm_norm] at ht
        have htpos : 0 < ‖t‖ ^ m := pow_pos (norm_pos_iff.mpr (by simpa using ht0)) m
        refine le_of_mul_le_mul_left ?_ htpos
        calc ‖t‖ ^ m * ‖p m (fun _ => y0)‖ ≤ C * (‖t‖ ^ (m + 1) * ‖y0‖ ^ (m + 1)) := by
              linarith [ht]
          _ = ‖t‖ ^ m * (C * ‖y0‖ ^ (m + 1) * ‖t‖) := by ring
      have hlim : Tendsto (fun t : ℂ => C * ‖y0‖ ^ (m + 1) * ‖t‖) (𝓝[≠] 0) (𝓝 0) := by
        have hc : Continuous fun t : ℂ => C * ‖y0‖ ^ (m + 1) * ‖t‖ :=
          continuous_const.mul continuous_norm
        have := hc.tendsto 0
        simpa using this.mono_left nhdsWithin_le_nhds
      have hc0 : ‖p m (fun _ => y0)‖ ≤ 0 := ge_of_tendsto hlim hbd
      exact norm_le_zero_iff.mp hc0
  refine ⟨p d, ?_⟩
  have hA := hp.isBigO_sub_partialSum_pow (d + 1)
  have hps : ∀ y : V n, p.partialSum (d + 1) y = p d (fun _ => y) := by
    intro y
    simp only [FormalMultilinearSeries.partialSum, Finset.sum_range_succ]
    rw [Finset.sum_eq_zero (fun j hj => hvan j (Finset.mem_range.mp hj) y), zero_add]
  simp only [zero_add, hps] at hA
  exact hA
end ReciprocityTheory.ChartRestriction.G.AR.Up.DivLA
