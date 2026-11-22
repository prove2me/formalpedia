-- Prove2me | solution 1 for PI.QnHermHaar.Gen.A_ext
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T19:59:58.245507+00:00
-- url     : https://prove2.me/submissions/9f36623c-c0f7-4a1b-bd95-e4a287da6b70

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HermitianHaarMeasure_RepOnAlgebraMap

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
noncomputable section
open PI PI.QnHermHaar PI.QnHermHaar.Gen
variable {α β : Type*} [MeasurableSpace α]
variable {μ : Measure α} {ι : α → β} {𝓕 : Submodule ℂ (β → ℂ)}
variable (hI : IntOn μ ι 𝓕)
namespace PI.QnHermHaar.Gen
theorem _root_.solution {S T : A hI}
    (h : ∀ f ∈ 𝓕, (S : Module.End ℂ (X hI)) (mk' hI f) = (T : Module.End ℂ (X hI)) (mk' hI f)) : S = T := by
  apply Subtype.ext
  apply LinearMap.ext
  intro x
  obtain ⟨f, hf, rfl⟩ := mk'_surj hI x
  exact h f hf
end PI.QnHermHaar.Gen
