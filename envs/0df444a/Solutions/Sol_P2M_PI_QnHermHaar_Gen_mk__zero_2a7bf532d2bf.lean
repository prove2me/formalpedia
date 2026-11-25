-- Prove2me | solution 1 for P2M_PI_QnHermHaar_Gen_mk__zero_2a7bf532d2bf
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T05:25:43.715609+00:00
-- url     : https://prove2.me/submissions/8cecc623-0770-43c9-9525-cb4bcb2fb59d

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
theorem _root_.solution : mk' hI (0 : β → ℂ) = 0 := by
  rw [mk'_of hI 𝓕.zero_mem]
  exact (Submodule.Quotient.mk_eq_zero _).mpr (N hI).zero_mem
end PI.QnHermHaar.Gen
