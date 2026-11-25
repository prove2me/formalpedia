-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.HExp.distortion
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:34:23.639724+00:00
-- url     : https://prove2.me/submissions/a2dba172-c2cd-4541-8da3-7243744b4146

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_FormalDegree_HaarVolumes_HaarExpA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_FormalDegree_HaarVolumes_HaarExpB
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_HExp_logA_exp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_HExp_exp_logA
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_HExp_logA_one
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_HExp_exp_cont
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_HExp_exp_neg_mul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_HExp_hasStrictFDerivAt_translateLog
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_HExp_hasStrictFDerivAt_productLog
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_HExp_eventually_pair
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_HExp_strict_est

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.HExp
open Filter Topology Metric NormedSpace Asymptotics
variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸]
namespace ReciprocityTheory.ChartRestriction.DS.HExp
theorem _root_.solution {ε : ℝ} (hε : 0 < ε) : ∃ δ > 0, ∀ X Y : 𝔸, ‖X‖ < δ → ‖Y‖ < δ →
    (exp (F1 (X, Y)) = exp (-X) * exp (X + Y) ∧ ‖F1 (X, Y) - Y‖ ≤ ε * ‖Y‖) ∧
    (exp (F2 (X, Y)) = exp X * exp Y ∧ ‖F2 (X, Y) - X - Y‖ ≤ ε * ‖Y‖) := by
  obtain ⟨δ1, h1, H1⟩ := strict_est (hasStrictFDerivAt_translateLog (𝔸 := 𝔸)) hε
  obtain ⟨δ2, h2, H2⟩ := strict_est (hasStrictFDerivAt_productLog (𝔸 := 𝔸)) hε
  have c1 : Tendsto (fun p : 𝔸 × 𝔸 => exp (-p.1) * exp (p.1 + p.2)) (𝓝 0) (𝓝 1) := by
    have : Continuous (fun p : 𝔸 × 𝔸 => exp (-p.1) * exp (p.1 + p.2)) :=
      (exp_cont.comp continuous_fst.neg).mul (exp_cont.comp (continuous_fst.add continuous_snd))
    have h := this.tendsto 0
    simpa [exp_zero] using h
  have c2 : Tendsto (fun p : 𝔸 × 𝔸 => exp p.1 * exp p.2) (𝓝 0) (𝓝 1) := by
    have : Continuous (fun p : 𝔸 × 𝔸 => exp p.1 * exp p.2) :=
      (exp_cont.comp continuous_fst).mul (exp_cont.comp continuous_snd)
    have h := this.tendsto 0
    simpa [exp_zero] using h
  obtain ⟨δ3, h3, H3⟩ := eventually_pair (c1.eventually exp_logA)
  obtain ⟨δ4, h4, H4⟩ := eventually_pair (c2.eventually exp_logA)
  obtain ⟨δ5, h5, H5⟩ := Metric.eventually_nhds_iff_ball.mp (logA_exp (𝔸 := 𝔸))
  refine ⟨min (min δ1 δ2) (min (min δ3 δ4) δ5), by positivity, fun X Y hX hY => ?_⟩
  simp only [lt_min_iff] at hX hY
  refine ⟨⟨H3 X Y hX.2.1.1 hY.2.1.1, ?_⟩, ⟨H4 X Y hX.2.1.2 hY.2.1.2, ?_⟩⟩
  · have := H1 X Y hX.1.1 hY.1.1
    have e : F1 (X, (0 : 𝔸)) = 0 := by simp [F1, exp_neg_mul, logA_one]
    simpa [e] using this
  · have := H2 X Y hX.1.2 hY.1.2
    have e : F2 (X, (0 : 𝔸)) = X := by
      simp only [F2, exp_zero, mul_one]
      exact H5 X (by simpa using hX.2.2)
    simpa [e] using this
end ReciprocityTheory.ChartRestriction.DS.HExp
