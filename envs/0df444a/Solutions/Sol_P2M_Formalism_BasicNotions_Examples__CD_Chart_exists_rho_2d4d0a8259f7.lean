-- Prove2me | solution 1 for P2M_Formalism_BasicNotions_Examples__CD_Chart_exists_rho_2d4d0a8259f7
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:03:15.693022+00:00
-- url     : https://prove2.me/submissions/87d12594-28bb-422d-a0e6-5208445b60c6

import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_LeOfEventuallyDown
import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_HasStrictFDerivAtExpZero
import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_ExistsDensity
import Theorems.Thm_P2M_Formalism_BasicNotions_Examples__CD_logA_exp_60d72a73aded


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
namespace Formalism.BasicNotions.Examples₂.CD.Chart
theorem _root_.solution : ∃ ρ > 0, ∀ Z : 𝔸, ‖Z‖ < ρ →
    logA 𝔸 (exp Z) = Z ∧ ((∃ g, C.mat g = exp Z) → Z ∈ V) := by
  obtain ⟨ε, hε, h⟩ := Metric.eventually_nhds_iff.1 ((logA_exp (𝔸 := 𝔸)).and C.H2)
  exact ⟨ε, hε, fun Z hZ => h (by simpa [dist_zero_right] using hZ)⟩
end Formalism.BasicNotions.Examples₂.CD.Chart
