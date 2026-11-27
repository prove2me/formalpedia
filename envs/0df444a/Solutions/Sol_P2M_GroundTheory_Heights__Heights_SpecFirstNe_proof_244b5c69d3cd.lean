-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_SpecFirstNe_proof_244b5c69d3cd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T05:08:19.635933+00:00
-- url     : https://prove2.me/submissions/d9f904e6-3f8c-41a3-ad1d-0e48ced02895

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_StatementsSectionOrder
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_PSpecFirstNe
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_exists_specFirst_ne_zero_e3165fe98c76
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_det_mulLeft_ne_zero_354addb8ade2

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
open MvPolynomial
noncomputable section
namespace GroundTheory.Heights₂.Heights
namespace SpecFirstNe
theorem _root_.solution (h₁ : IncIdealBelow.Statement) (h₂ : SpecFirstMemIncIdeal.Statement)
    (h₄ : ChartLocDomain.Statement) (h₅ : ChartNorm.Statement) : SpecFirstNe.Statement := by
  intro F _ _ n e I f u hI hf hu
  obtain ⟨t, ht⟩ := exists_specFirst_ne_zero hf.1
  have hlt : linForm t ∉ I := fun hmem => ht (by
    have hmem' := h₂ F n e I I f t hf le_rfl hmem
    rwa [h₁ F n e I f hI hf, Ideal.mem_bot] at hmem')
  have htp : specFirst f t ∉ (⊥ : Ideal (MvPolynomial (Fin e × Fin n) F)) := by
    rwa [Ideal.mem_bot]
  obtain ⟨hdom, -, hθ⟩ := h₄ F n e I f t ⊥ hI hf hlt
  have hnorm := h₅ F n e I f t ⊥ hI hf (Or.inl rfl) htp u
  have ha : algebraMap _ (Localization.AtPrime (⊥ : Ideal (MvPolynomial (Fin e × Fin n) F)))
      (specFirst f t) ≠ 0 := fun h => ht
    (IsLocalization.injective (Localization.AtPrime (⊥ : Ideal (MvPolynomial (Fin e × Fin n) F)))
      (Ideal.primeCompl_le_nonZeroDivisors ⊥) (h.trans (map_zero _).symm))
  have hdet := det_mulLeft_ne_zero (O := Localization.AtPrime (⊥ : Ideal (MvPolynomial (Fin e × Fin n) F)))
    (hθ u hu)
  intro h0
  rw [h0, map_zero] at hnorm
  exact mul_ne_zero ha hdet hnorm.symm
end SpecFirstNe
end GroundTheory.Heights₂.Heights
