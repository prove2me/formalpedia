-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_blowUpOf_mono_79a813d4a6e9
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T04:41:47.915456+00:00
-- url     : https://prove2.me/submissions/95dd1275-e25a-439e-a267-e26379e4761a

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsBlowUpHorizontal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_LiftFormNotMemBlowUpOf
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PBlowUpHorizontalStrict

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.NumbersDVR
open MvPolynomial
universe u
noncomputable section
set_option linter.unusedSectionVars false
variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} {J : Type} {R : Type*} [CommRing R]
namespace GroundTheory.Heights₂.Heights.NumbersDVR
theorem _root_.solution {P W : Ideal (MRing ι R)} (h : P ≤ W) (u : J → MRing ι R) :
    blowUpOf P u ≤ blowUpOf W u := by
  intro F hF
  let φ := Polynomial.mapRingHom (Ideal.Quotient.factor h)
  have key : φ.comp (aeval (R := R) (blowUpSubst P u)).toRingHom =
      (aeval (R := R) (blowUpSubst W u)).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [φ]
      rfl
    · rintro ⟨_ | k, i⟩
      · simp [φ, blowUpSubst, Ideal.Quotient.factor_mk]
      · simp [φ, blowUpSubst, Ideal.Quotient.factor_mk]
  have e := DFunLike.congr_fun key F
  simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom] at e
  rw [blowUpOf, RingHom.mem_ker] at hF ⊢
  rw [← e, hF, map_zero]
end GroundTheory.Heights₂.Heights.NumbersDVR
