-- Prove2me | solution 1 for P2M_Formalism_BasicNotions_Examples__CD_Chart_injOn_8b27bc3b6990
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T00:32:20.614889+00:00
-- url     : https://prove2.me/submissions/820f6fef-08c0-40ca-89bc-4c6fb099daba

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
variable {ρ : ℝ} (hR : ∀ Z : 𝔸, ‖Z‖ < ρ → logA 𝔸 (exp Z) = Z ∧ ((∃ g, C.mat g = exp Z) → Z ∈ V))
include hR
namespace Formalism.BasicNotions.Examples₂.CD.Chart
theorem _root_.solution : InjOn C.expG (ball (0 : V) ρ) := by
  intro X hX Y hY hXY
  have h1 : exp (X : 𝔸) = exp (Y : 𝔸) := by
    rw [← C.mat_expG, ← C.mat_expG, hXY]
  have hXn : ‖(X : 𝔸)‖ < ρ := by simpa using hX
  have hYn : ‖(Y : 𝔸)‖ < ρ := by simpa using hY
  apply Subtype.ext
  rw [← (hR _ hXn).1, ← (hR _ hYn).1, h1]
end Formalism.BasicNotions.Examples₂.CD.Chart
