-- Prove2me | solution 1 for PI.QnHermHaar.Gen.repOn_algebraMap
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:43:25.587827+00:00
-- url     : https://prove2.me/submissions/a50842e1-4d04-4b69-9508-ed7f73c79983

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HermitianHaarMeasure_RepOnAlgebraMap
import Theorems.Thm_PI_QnHermHaar_Gen_repOn_smul
import Theorems.Thm_PI_QnHermHaar_Gen_repOn_one

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
theorem _root_.solution (c : ℂ) : RepOn hI (algebraMap ℂ (A hI) c) (fun f => c • f) := by
  rw [Algebra.algebraMap_eq_smul_one]
  exact repOn_smul hI c (repOn_one hI)
end PI.QnHermHaar.Gen
