-- Prove2me | solution 1 for P2M_Formalism_BasicNotions_Examples__CD_Chart_nu_finite_542036c95c54
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:30:51.231652+00:00
-- url     : https://prove2.me/submissions/f9b018d4-d6ad-4f57-98f2-af065b236059

import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_LeOfEventuallyDown
import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_HasStrictFDerivAtExpZero
import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_ExistsDensity
import Theorems.Thm_P2M_Formalism_BasicNotions_Examples__CD_Chart_expG_cont_48656f8a7b66
import Theorems.Thm_P2M_Formalism_BasicNotions_Examples__CD_Chart_nu_apply_3ee47408ca0b

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
theorem _root_.solution : IsFiniteMeasure (C.nu ρ μ) := by
  constructor
  rw [C.nu_apply hR μ MeasurableSet.univ, Set.univ_inter]
  have hK : IsCompact (C.expG '' closedBall (0 : V) ρ) := (isCompact_closedBall 0 ρ).image C.expG_cont
  exact lt_of_le_of_lt (measure_mono (Set.image_mono ball_subset_closedBall)) hK.measure_lt_top
end Formalism.BasicNotions.Examples₂.CD.Chart
