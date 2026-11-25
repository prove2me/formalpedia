-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_LatticeLemmas_HadamardQuotient_normAt_mkQ_le_f55819c0c9d0
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T09:38:52.012335+00:00
-- url     : https://prove2.me/submissions/6f854d08-3a37-4c1b-b801-5c11623d2fdf

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_PHadamardQuotient
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
open NumberField NumberField.ComplexEmbedding TensorProduct ComplexAt Module Submodule
open GroundTheory.Heights₂.Heights
universe u v w
noncomputable section
open GroundTheory.Heights₂.Heights.LatticeLemmas.HadamardQuotient
variable {K : Type*} [Field K] [NumberField K]
namespace GroundTheory.Heights₂.Heights.LatticeLemmas.HadamardQuotient
theorem _root_.solution (M : HermitianBundle K) (F : Submodule (𝓞 K) M.carrier) (hF : M.Saturated F)
    (σ : K →+* ℂ) (x : M.carrier) :
    (M.quot F hF).normAt σ (F.mkQ x) ≤ M.normAt σ x := by
  have h := HermitianBundle.quot_norm_eq_iInf M F hF σ
    ((1 : ComplexAt σ) ⊗ₜ[𝓞 K] (F.mkQ x : M.carrier ⧸ F))
  refine (le_of_eq h).trans ?_
  exact ciInf_le ⟨0, by rintro _ ⟨y, rfl⟩; exact norm_nonneg _⟩
    (⟨(1 : ComplexAt σ) ⊗ₜ[𝓞 K] x, rfl⟩ :
      {y : Fibre σ M.carrier // F.mkQ.lTensor (ComplexAt σ) y = (1 : ComplexAt σ) ⊗ₜ[𝓞 K] F.mkQ x})
end GroundTheory.Heights₂.Heights.LatticeLemmas.HadamardQuotient
