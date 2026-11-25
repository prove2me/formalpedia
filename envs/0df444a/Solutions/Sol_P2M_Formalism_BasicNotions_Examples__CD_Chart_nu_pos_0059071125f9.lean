-- Prove2me | solution 1 for P2M_Formalism_BasicNotions_Examples__CD_Chart_nu_pos_0059071125f9
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:30:52.858463+00:00
-- url     : https://prove2.me/submissions/37658c2e-49fd-4a22-8125-4f66838a7081

import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_LeOfEventuallyDown
import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_HasStrictFDerivAtExpZero
import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_ExistsDensity
import Theorems.Thm_P2M_Formalism_BasicNotions_Examples__CD_Chart_mat_expG_1363518d9b59
import Theorems.Thm_P2M_Formalism_BasicNotions_Examples__CD_Chart_nu_apply_3ee47408ca0b
import Theorems.Thm_P2M_Formalism_BasicNotions_Examples__CD_exp_logA_34b3c58efbe1
import Theorems.Thm_P2M_Formalism_BasicNotions_Examples__CD_hasStrict_logA_de7a3d570658
import Theorems.Thm_P2M_Formalism_BasicNotions_Examples__CD_logA_one_5d3ec8a2de84


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Examples₂ Formalism.BasicNotions.Examples₂.CD
open MeasureTheory Filter Topology Metric NormedSpace Set
open scoped ENNReal NNReal
variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸]
open Formalism.BasicNotions.Examples₂.CD.Chart
variable {V : Submodule ℝ 𝔸} {G : Type*} [Group G] [TopologicalSpace G] (C : Chart V G)
variable {ρ : ℝ} (hR : ∀ Z : 𝔸, ‖Z‖ < ρ → logA 𝔸 (exp Z) = Z ∧ ((∃ g, C.mat g = exp Z) → Z ∈ V))
variable [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
  [MeasurableSpace G] [BorelSpace G]
variable (μ : Measure G)
variable [IsTopologicalGroup G] [μ.IsHaarMeasure]
include hR
namespace Formalism.BasicNotions.Examples₂.CD.Chart
theorem _root_.solution (hρ : 0 < ρ) (r : ℝ) (hr : 0 < r) : 0 < C.nu ρ μ (closedBall (0 : V) r) := by
  have ht : 0 < min r ρ := lt_min hr hρ
  have hcont : ContinuousAt (logA 𝔸) 1 := (hasStrict_logA (𝔸 := 𝔸)).hasFDerivAt.continuousAt
  have hlim : Tendsto (logA 𝔸) (𝓝 1) (𝓝 0) := by
    have h := hcont.tendsto
    rwa [logA_one] at h
  have hev : ∀ᶠ h in 𝓝 (1 : 𝔸), exp (logA 𝔸 h) = h ∧ ‖logA 𝔸 h‖ < min r ρ := by
    refine (exp_logA (𝔸 := 𝔸)).and ?_
    filter_upwards [(Metric.tendsto_nhds.1 hlim) _ ht] with h hh
    simpa [dist_zero_right] using hh
  obtain ⟨W, hWsub, hWo, hW1⟩ := _root_.mem_nhds_iff.1 hev
  have hUo : IsOpen (C.mat ⁻¹' W) := hWo.preimage C.emb.continuous
  have hU1 : (1 : G) ∈ C.mat ⁻¹' W := by
    show C.mat 1 ∈ W
    rw [map_one]
    exact hW1
  have hsub : C.mat ⁻¹' W ⊆ C.expG '' (closedBall 0 r ∩ ball 0 ρ) := by
    intro g hg
    obtain ⟨he, hn⟩ := hWsub hg
    have hZρ : ‖logA 𝔸 (C.mat g)‖ < ρ := lt_of_lt_of_le hn (min_le_right _ _)
    have hZV : logA 𝔸 (C.mat g) ∈ V := (hR _ hZρ).2 ⟨g, he.symm⟩
    refine ⟨⟨logA 𝔸 (C.mat g), hZV⟩, ⟨?_, ?_⟩, ?_⟩
    · rw [mem_closedBall_zero_iff]
      exact le_of_lt (lt_of_lt_of_le hn (min_le_left _ _))
    · rw [mem_ball_zero_iff]
      exact hZρ
    · apply C.emb.injective
      rw [C.mat_expG]
      exact he
  rw [C.nu_apply hR μ measurableSet_closedBall]
  exact lt_of_lt_of_le (hUo.measure_pos μ ⟨1, hU1⟩) (measure_mono hsub)
end Formalism.BasicNotions.Examples₂.CD.Chart
