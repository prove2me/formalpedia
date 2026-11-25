-- Prove2me | solution 1 for PI.QnHermHaar.Gen.repOn_intCast
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:08:05.620815+00:00
-- url     : https://prove2.me/submissions/e6422836-784b-4bbf-b660-3aaada127199

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HermitianHaarMeasure_RepOnAlgebraMap
import Theorems.Thm_PI_QnHermHaar_Gen_repOn_algebraMap

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
theorem _root_.solution (n : ℤ) : RepOn hI ((n : A hI)) (fun f => (n : ℂ) • f) := by
  rw [← map_intCast (algebraMap ℂ (A hI)) n]
  exact repOn_algebraMap hI (n : ℂ)
end PI.QnHermHaar.Gen
