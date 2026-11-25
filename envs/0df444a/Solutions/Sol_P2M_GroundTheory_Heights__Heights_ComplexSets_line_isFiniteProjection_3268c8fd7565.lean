-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ComplexSets_line_isFiniteProjection_3268c8fd7565
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T04:28:51.58191+00:00
-- url     : https://prove2.me/submissions/228004e6-9f23-40de-aba0-e264534b37d7

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_Statements
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ComplexSets_pullback_one_b525a2fbfb79

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.ComplexSets
open MvPolynomial Pointwise
noncomputable section
variable {n d : ℕ}
namespace GroundTheory.Heights₂.Heights.ComplexSets
theorem _root_.solution :
    IsFiniteProjection (⊥ : Ideal (MvPolynomial (Fin 1) ℂ)) (1 : Matrix (Fin 1) (Fin 1) ℂ) := by
  have hb : Function.Bijective (Ideal.Quotient.mkₐ ℂ (⊥ : Ideal (MvPolynomial (Fin 1) ℂ))) :=
    (Ideal.Quotient.mk_bijective_iff_eq_bot _).mpr rfl
  have he : (projHom (⊥ : Ideal (MvPolynomial (Fin 1) ℂ)) (1 : Matrix (Fin 1) (Fin 1) ℂ) :
      MvPolynomial (Fin 1) ℂ → _) = Ideal.Quotient.mkₐ ℂ _ := by
    rw [projHom, pullback_one, AlgHom.comp_id]
  refine ⟨?_, ?_⟩
  · rw [he]; exact hb.1
  · apply RingHom.Finite.of_surjective
    change Function.Surjective (projHom _ _ : MvPolynomial (Fin 1) ℂ → _)
    rw [he]; exact hb.2
end GroundTheory.Heights₂.Heights.ComplexSets
