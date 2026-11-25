-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Theta_conj_eq_complexConj_3315d27272de
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T09:19:11.663185+00:00
-- url     : https://prove2.me/submissions/12f31473-d5a1-4d9e-b0f2-4f894c10437b

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_QuadraticConj
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_CMDatum
import Theorems.Thm_P2M_GroundTheory_Heights__Theta_complexConjOver_apply_a73e4a8899a9
import Theorems.Thm_P2M_GroundTheory_Heights__Theta_conj_ne_one_53767739c25f
import Theorems.Thm_GroundTheory_Automorphic_conj_conj
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Automorphic.conj_conj



set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Theta
open NumberField GroundTheory.Automorphic
variable (F E : Type*) [Field F] [NumberField F] [IsTotallyReal F] [Field E] [NumberField E]
  [IsTotallyComplex E] [Algebra F E] [Algebra.IsQuadraticExtension F E]
variable {F E}
variable (F E)
namespace GroundTheory.Heights₂.Theta
theorem _root_.solution (x : E) :
    haveI := isCMField F E
    conj F E x = IsCMField.complexConj E x := by
  haveI := isCMField F E
  have hcard : Nat.card (E ≃ₐ[F] E) = 2 := by
    rw [IsGalois.card_aut_eq_finrank, Algebra.IsQuadraticExtension.finrank_eq_two]
  have hσ : complexConjOver F E ≠ 1 := by
    intro h
    apply IsCMField.complexConj_ne_one E
    ext y
    have := congrArg (fun g : E ≃ₐ[F] E => g y) h
    simpa [complexConjOver_apply] using this
  have huniq := (Nat.card_eq_two_iff' (1 : E ≃ₐ[F] E)).1 hcard
  have := huniq.unique (conj_ne_one F E) hσ
  rw [this, complexConjOver_apply]
end GroundTheory.Heights₂.Theta
