-- Prove2me | solution 1 for P2M_PI_QnHermHaar_Gen_mk__neg_9a326db1785f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T05:25:42.39322+00:00
-- url     : https://prove2.me/submissions/4700f3c8-6e1d-4400-8ac4-0791f8662a9b

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
theorem _root_.solution {f : β → ℂ} (hf : f ∈ 𝓕) : mk' hI (-f) = -mk' hI f := by
  rw [mk'_of hI (𝓕.neg_mem hf), mk'_of hI hf, ← Submodule.Quotient.mk_neg]
  rfl
end PI.QnHermHaar.Gen
