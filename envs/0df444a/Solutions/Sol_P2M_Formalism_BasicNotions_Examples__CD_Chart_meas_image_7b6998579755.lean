-- Prove2me | solution 1 for P2M_Formalism_BasicNotions_Examples__CD_Chart_meas_image_7b6998579755
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:40:03.157783+00:00
-- url     : https://prove2.me/submissions/9e9863f0-cf4b-4cd4-b6f7-a86e386aabd6

import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_LeOfEventuallyDown
import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_HasStrictFDerivAtExpZero
import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_ExistsDensity
import Theorems.Thm_P2M_Formalism_BasicNotions_Examples__CD_Chart_expG_cont_48656f8a7b66
import Theorems.Thm_P2M_Formalism_BasicNotions_Examples__CD_Chart_injOn_8b27bc3b6990

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
include hR
namespace Formalism.BasicNotions.Examples₂.CD.Chart
theorem _root_.solution {s : Set V} (hs : MeasurableSet s) (hsub : s ⊆ ball 0 ρ) :
    MeasurableSet (C.expG '' s) := by
  haveI : T2Space G := C.emb.t2Space
  haveI : CompleteSpace V := FiniteDimensional.complete ℝ V
  exact hs.image_of_continuousOn_injOn C.expG_cont.continuousOn ((C.injOn hR).mono hsub)
end Formalism.BasicNotions.Examples₂.CD.Chart
