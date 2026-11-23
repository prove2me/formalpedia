-- Prove2me | solution 1 for PI.QnHermHaar.Gen.repOn_toA
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:17:06.670335+00:00
-- url     : https://prove2.me/submissions/c615ff86-356c-41f0-aeeb-8de018efff39

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HermitianHaarMeasure_RepOnAlgebraMap
import Theorems.Thm_P2M_PI_QnHermHaar_Gen_toA_mk__50be6af2c076

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
theorem _root_.solution {Φ Φ' : (β → ℂ) → (β → ℂ)} (hΦ : AdjOp (μ := μ) (ι := ι) (𝓕 := 𝓕) G Φ Φ') :
    RepOn hI (toA hI hG hΦ) Φ := fun f hf => ⟨hΦ.mem f hf, toA_mk' hI hG hΦ hf⟩
end PI.QnHermHaar.Gen
