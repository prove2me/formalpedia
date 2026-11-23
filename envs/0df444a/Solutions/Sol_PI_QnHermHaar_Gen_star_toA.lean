-- Prove2me | solution 1 for PI.QnHermHaar.Gen.star_toA
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:40:20.024831+00:00
-- url     : https://prove2.me/submissions/31a3dfe4-bf60-480c-b67c-0cf57d8a108b

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
    star (toA hI hG hΦ) = toA hI hG hΦ.symm := by
  apply star_eq_of
  intro x y
  obtain ⟨f, hf, rfl⟩ := mk'_surj hI x
  obtain ⟨h, hh, rfl⟩ := mk'_surj hI y
  rw [toA_mk' hI hG hΦ hf, toA_mk' hI hG hΦ.symm hh,
    ip_mk' hI (hΦ.mem _ hf) hh, ip_mk' hI hf (hΦ.mem' _ hh)]
  exact hΦ.adj f hf h hh
end PI.QnHermHaar.Gen
