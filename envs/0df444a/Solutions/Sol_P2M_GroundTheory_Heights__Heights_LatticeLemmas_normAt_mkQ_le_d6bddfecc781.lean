-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_LatticeLemmas_normAt_mkQ_le_d6bddfecc781
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T09:39:12.234988+00:00
-- url     : https://prove2.me/submissions/feae088e-e747-4864-a235-db3e3671244a

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_PHadamardMeanQuotient
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HermitianBundle_quot_norm_eq_iInf_945d17c91762


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LatticeLemmas
open NumberField GroundTheory.Heights₂.Heights Submodule Cardinal TensorProduct
universe u v w
noncomputable section
variable {K : Type u} [Field K] [NumberField K]
namespace GroundTheory.Heights₂.Heights.LatticeLemmas
theorem _root_.solution (M : HermitianBundle.{v} K) (F : Submodule (𝓞 K) M.carrier)
    (hF : M.Saturated F) (σ : K →+* ℂ) (e : M.carrier) :
    (M.quot F hF).normAt σ (F.mkQ e) ≤ M.normAt σ e := by
  have h := HermitianBundle.quot_norm_eq_iInf M F hF σ ((1 : ComplexAt σ) ⊗ₜ[𝓞 K] F.mkQ e)
  refine (le_of_eq h).trans ?_
  exact ciInf_le ⟨0, by rintro _ ⟨y, rfl⟩; exact norm_nonneg _⟩
    (⟨(1 : ComplexAt σ) ⊗ₜ[𝓞 K] e, by simp⟩ :
      {y : Fibre σ M.carrier // F.mkQ.lTensor (ComplexAt σ) y = (1 : ComplexAt σ) ⊗ₜ[𝓞 K] F.mkQ e})
end GroundTheory.Heights₂.Heights.LatticeLemmas
