-- Prove2me | solution 1 for Sennott1989.AvgCost.lemma_A2
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-06T07:18:58.445417+00:00
-- url     : https://prove2.me/submissions/7bee3d01-eaf3-4809-95e1-b62841c2e159

import Mathlib
import Definitions.Def_Sennott1989_AvgCost_Assumptions
import Theorems.Thm_SennottDP_Tauberian_abelian_inequalities

open scoped ENNReal NNReal
open Filter Topology

open SennottDP.Discounted in
theorem solution {Act : Type} (M : MDC ℕ Act) (θ : Policy M) (i : ℕ) :
    limsup (fun α : ℝ≥0 => ((1 - α : ℝ≥0) : ℝ≥0∞) * valueFn M α i) (𝓝[<] 1) ≤
      SennottDP.SEN.avgCost M θ i := by
  set u : ℕ → ℝ≥0∞ := fun t => expCost M θ i t with hu
  by_cases hu0 : u 0 = ⊤
  · have : SennottDP.SEN.avgCost M θ i = ⊤ := by
      unfold SennottDP.SEN.avgCost
      have hev : (fun n : ℕ => SennottDP.SEN.horizonCost M θ n i / (n : ℝ≥0∞)) =ᶠ[atTop]
          fun _ => ⊤ := by
        filter_upwards [eventually_ge_atTop 1] with n hn
        have h1 : SennottDP.SEN.horizonCost M θ n i = ⊤ := by
          unfold SennottDP.SEN.horizonCost
          refine top_le_iff.1 ?_
          rw [← hu0]
          exact Finset.single_le_sum (f := fun t => expCost M θ i t) (fun _ _ => bot_le)
            (Finset.mem_range.2 (by omega))
        rw [h1, ENNReal.top_div_of_ne_top (ENNReal.natCast_ne_top n)]
      rw [limsup_congr hev, limsup_const]
    rw [this]; exact le_top
  · have hab := (SennottDP.Tauberian.abelian_inequalities u hu0).2.2
    calc limsup (fun α : ℝ≥0 => ((1 - α : ℝ≥0) : ℝ≥0∞) * valueFn M α i) (𝓝[<] 1)
        ≤ limsup (SennottDP.Tauberian.abelMean u) (𝓝[<] (1 : ℝ≥0)) := by
          refine limsup_le_limsup (Eventually.of_forall fun α => ?_)
          unfold SennottDP.Tauberian.abelMean SennottDP.Tauberian.U
          show ((1 - α : ℝ≥0) : ℝ≥0∞) * valueFn M α i ≤ _
          rw [ENNReal.coe_sub, ENNReal.coe_one]
          exact mul_le_mul_right (iInf_le _ θ) _
      _ ≤ limsup (SennottDP.Tauberian.cesaroMean u) atTop := hab
      _ = SennottDP.SEN.avgCost M θ i := rfl
