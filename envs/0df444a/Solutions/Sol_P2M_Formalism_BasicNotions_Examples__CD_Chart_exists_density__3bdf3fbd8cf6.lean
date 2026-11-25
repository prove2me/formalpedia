-- Prove2me | solution 1 for P2M_Formalism_BasicNotions_Examples__CD_Chart_exists_density__3bdf3fbd8cf6
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T04:18:48.116884+00:00
-- url     : https://prove2.me/submissions/83a88714-5c21-4560-9b9b-0f009ff52d96

import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_LeOfEventuallyDown
import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_HasStrictFDerivAtExpZero
import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_ExistsDensity
import Theorems.Thm_P2M_Formalism_BasicNotions_Examples__CD_Chart_exists_density_1ad0f7fa557c
import Theorems.Thm_P2M_Formalism_BasicNotions_Examples__CD_exists_density_03e233a4d5e1


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
namespace Formalism.BasicNotions.Examples₂.CD
namespace Chart
theorem _root_.solution {V : Submodule ℝ 𝔸} {G : Type*} [Group G] [TopologicalSpace G]
    (C : Chart V G) (_hfd : FiniteDimensional ℝ V) (mV : MeasurableSpace V) (_hbV : BorelSpace V)
    (mG : MeasurableSpace G) (_hbG : BorelSpace G) (_hG : IsTopologicalGroup G)
    (μ : Measure G) (_hμ : μ.IsHaarMeasure) (lam : Measure V) (_hlam : lam.IsAddHaarMeasure) :
    ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ⊤ ∧ ∀ S : ℝ → Set V, (∀ r, MeasurableSet (S r)) →
      (∀ δ > 0, ∀ᶠ r in 𝓝[>] (0 : ℝ), ∀ X ∈ S r, ‖(X : 𝔸)‖ < δ) →
      (∀ᶠ r in 𝓝[>] (0 : ℝ), lam (S r) ≠ 0 ∧ lam (S r) ≠ ⊤) →
      Tendsto (fun r => μ {g | ∃ X ∈ S r, C.mat g = exp ((X : V) : 𝔸)} / lam (S r)) (𝓝[>] 0) (𝓝 c) := by
  letI := mV
  letI := mG
  haveI := _hfd
  haveI := _hbV
  haveI := _hbG
  haveI := _hG
  haveI := _hμ
  haveI := _hlam
  obtain ⟨c, h0, h1, h⟩ := C.exists_density μ lam
  refine ⟨c, h0, h1, fun S hS hsm hl => h S hS (fun δ hδ => (hsm δ hδ).mono fun r hr X hX => ?_) hl⟩
  simpa using hr X hX
end Chart
end Formalism.BasicNotions.Examples₂.CD
