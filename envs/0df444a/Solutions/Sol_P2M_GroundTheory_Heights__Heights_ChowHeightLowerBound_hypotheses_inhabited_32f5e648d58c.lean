-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ChowHeightLowerBound_hypotheses_inhabited_32f5e648d58c
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T08:54:41.55689+00:00
-- url     : https://prove2.me/submissions/77248ae3-4a77-431b-b6ad-ae508810c242

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_Statements
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_isProjPrime_point_e4b734f59300
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_isChowForm_point_62847896aaea
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_isMultiHomog_point_50a43e297f77

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial MeasureTheory NumberField
noncomputable section
namespace GroundTheory.Heights₂.Heights
namespace ChowHeightLowerBound
theorem _root_.solution :
    IsProjPrime (⊥ : Ideal (MvPolynomial (Fin 1) ℚ)) ∧
      IsChowForm (⊥ : Ideal (MvPolynomial (Fin 1) ℚ)) (0 + 1) (X (0, 0)) ∧
      IsMultiHomog 1 (X (0, 0) : MvPolynomial (Fin (0 + 1) × Fin 1) ℚ) ∧
      Submodule.span (𝓞 ℚ) {(fun _ => 1 : Fin 1 → 𝓞 ℚ)} = ⊤ ∧
      (∀ s ∈ ({(fun _ => 1 : Fin 1 → 𝓞 ℚ)} : Set (Fin 1 → 𝓞 ℚ)), ∀ σ : ℚ →+* ℂ,
        ((ArchData.std ℚ 1).normAt σ).norm (fun j => σ (s j)) ≤ 1) := by
  refine ⟨isProjPrime_point ℚ, isChowForm_point ℚ, isMultiHomog_point ℚ, ?_, ?_⟩
  · rw [eq_top_iff]
    intro v _
    rw [Submodule.mem_span_singleton]
    exact ⟨v 0, funext fun j => by rw [Fin.fin_one_eq_zero j]; simp⟩
  · intro s hs σ
    rw [Set.mem_singleton_iff] at hs
    subst hs
    simp [ArchData.std, HermNorm.std, HermNorm.norm]
end ChowHeightLowerBound
end GroundTheory.Heights₂.Heights
