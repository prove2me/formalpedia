-- Prove2me | solution 1 for P2M_PI_QnHermHaar_Gen_toA_mk__50be6af2c076
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:13:27.978102+00:00
-- url     : https://prove2.me/submissions/d30a7ee5-e19b-442e-9007-7af2a344f643

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
variable (G : Set β) (hG : ∀ᵐ x ∂μ, ι x ∈ G)
variable {G}
variable (hG : ∀ᵐ x ∂μ, ι x ∈ G)
namespace PI.QnHermHaar.Gen
theorem _root_.solution {Φ Φ' : (β → ℂ) → (β → ℂ)} (hΦ : AdjOp (μ := μ) (ι := ι) (𝓕 := 𝓕) G Φ Φ')
    {f : β → ℂ} (hf : f ∈ 𝓕) : ((toA hI hG hΦ : A hI) : Module.End ℂ (X hI)) (mk' hI f) = mk' hI (Φ f) := opX_mk' hI hG hΦ hf
end PI.QnHermHaar.Gen
