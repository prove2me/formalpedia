-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_AreaGraph_proof_a2628c3abbdd
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:33:14.285804+00:00
-- url     : https://prove2.me/submissions/9fd12547-42ed-4b1d-b69f-fda46d1a92df

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StatementsArea
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StAreaGraphBound
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PAreaGraph

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
open MeasureTheory Filter Topology
open scoped ENNReal NNReal
namespace GroundTheory.Heights₂.Heights
namespace AreaGraph
theorem _root_.solution (h : AreaGraphBound.Statement) : AreaGraph.Statement := by
  intro k m U F hU hF A hAU hA

  change μH[(k : ℝ)] (realGraphPt F '' A) =
    ∫⁻ x in A, ENNReal.ofReal (graphJac (fderiv ℝ F x :
      EuclideanSpace ℝ (Fin k) →ₗ[ℝ] EuclideanSpace ℝ (Fin m))) ∂(μH[(k : ℝ)])
  set S := μH[(k : ℝ)] (realGraphPt F '' A)
  set I := ∫⁻ x in A, ENNReal.ofReal (graphJac (fderiv ℝ F x :
      EuclideanSpace ℝ (Fin k) →ₗ[ℝ] EuclideanSpace ℝ (Fin m))) ∂(μH[(k : ℝ)])

  have hplus : ∀ j : ℕ,
      Tendsto (fun δ : ℝ≥0 => ((1 + δ : ℝ≥0) : ℝ≥0∞) ^ j) (𝓝[>] 0) (𝓝 1) := by
    intro j
    have hcont : Continuous (fun δ : ℝ≥0 => ((1 + δ : ℝ≥0) : ℝ≥0∞) ^ j) :=
      (ENNReal.continuous_pow j).comp (ENNReal.continuous_coe.comp (continuous_const.add continuous_id))
    simpa using (hcont.tendsto 0).mono_left nhdsWithin_le_nhds
  have hminus : ∀ j : ℕ,
      Tendsto (fun δ : ℝ≥0 => ((1 - δ : ℝ≥0) : ℝ≥0∞) ^ j) (𝓝[>] 0) (𝓝 1) := by
    intro j
    have hcont : Continuous (fun δ : ℝ≥0 => ((1 - δ : ℝ≥0) : ℝ≥0∞) ^ j) :=
      (ENNReal.continuous_pow j).comp (ENNReal.continuous_coe.comp (continuous_const.sub continuous_id))
    simpa using (hcont.tendsto 0).mono_left nhdsWithin_le_nhds

  have hev : ∀ᶠ δ in 𝓝[>] (0 : ℝ≥0), 0 < δ ∧ δ < 1 := by
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ≥0) < 1 from one_pos)] with δ hδ
    exact hδ
  have hb : ∀ᶠ δ in 𝓝[>] (0 : ℝ≥0),
      S ≤ ((1 + δ : ℝ≥0) : ℝ≥0∞) ^ (k + 1) * I ∧
        ((1 - δ : ℝ≥0) : ℝ≥0∞) ^ k * I ≤ ((1 + δ : ℝ≥0) : ℝ≥0∞) * S := by
    filter_upwards [hev] with δ hδ
    exact h k m U F hU hF A hAU hA δ hδ.1 hδ.2
  apply le_antisymm
  · have hlim := ENNReal.Tendsto.mul_const (hplus (k + 1)) (b := I) (Or.inl one_ne_zero)
    rw [one_mul] at hlim
    exact le_of_tendsto_of_tendsto tendsto_const_nhds hlim (hb.mono fun δ hδ => hδ.1)
  · have hlim₁ := ENNReal.Tendsto.mul_const (hminus k) (b := I) (Or.inl one_ne_zero)
    have hlim₂ := ENNReal.Tendsto.mul_const (by simpa using hplus 1) (b := S) (Or.inl one_ne_zero)
    rw [one_mul] at hlim₁ hlim₂
    exact le_of_tendsto_of_tendsto hlim₁ hlim₂ (hb.mono fun δ hδ => hδ.2)
end AreaGraph
end GroundTheory.Heights₂.Heights
