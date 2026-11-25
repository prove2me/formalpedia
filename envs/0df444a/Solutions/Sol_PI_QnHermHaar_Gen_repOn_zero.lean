-- Prove2me | solution 1 for PI.QnHermHaar.Gen.repOn_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T05:55:45.441011+00:00
-- url     : https://prove2.me/submissions/e3f570ec-a3aa-4e1d-bb99-ae8465392735

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HermitianHaarMeasure_RepOnAlgebraMap
import Theorems.Thm_P2M_PI_QnHermHaar_Gen_mk__zero_2a7bf532d2bf

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
variable (G : Set β) (hG : ∀ᵐ x ∂μ, ι x ∈ G)
variable {G}
variable (hG : ∀ᵐ x ∂μ, ι x ∈ G)
namespace PI.QnHermHaar.Gen
theorem _root_.solution : RepOn hI (0 : A hI) (fun _ => 0) := by
  intro _ _
  refine ⟨𝓕.zero_mem, ?_⟩
  show (0 : X hI) = mk' hI 0
  rw [mk'_zero]
end PI.QnHermHaar.Gen
