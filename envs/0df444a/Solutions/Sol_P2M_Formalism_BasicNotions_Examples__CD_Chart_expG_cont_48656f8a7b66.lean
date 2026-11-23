-- Prove2me | solution 1 for P2M_Formalism_BasicNotions_Examples__CD_Chart_expG_cont_48656f8a7b66
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:03:15.953405+00:00
-- url     : https://prove2.me/submissions/8bcfc576-392f-4038-9d75-648976ce6813

import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_LeOfEventuallyDown
import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_HasStrictFDerivAtExpZero
import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_ExistsDensity
import Theorems.Thm_P2M_Formalism_BasicNotions_Examples__CD_Chart_mat_expG_1363518d9b59

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
theorem _root_.solution : Continuous C.expG := by
  rw [C.emb.continuous_iff]
  have h : C.mat ∘ C.expG = fun X : V => exp (X : 𝔸) := funext C.mat_expG
  rw [h]
  have hc : Continuous (fun Z : 𝔸 => exp Z) := by
    first
      | exact NormedSpace.exp_continuous (𝕂 := ℝ)
      | exact (NormedSpace.exp_continuous (𝕂 := ℝ) (𝔸 := 𝔸))
      | exact continuous_iff_continuousAt.2 fun Z => (NormedSpace.exp_analytic (𝕂 := ℝ) Z).continuousAt
      | exact NormedSpace.exp_continuous
  exact hc.comp continuous_subtype_val
end Formalism.BasicNotions.Examples₂.CD.Chart
