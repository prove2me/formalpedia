-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_liftForm_not_mem_blowUpOf_1d9a7d35fe34
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T18:14:12.4898+00:00
-- url     : https://prove2.me/submissions/ff3a8695-7878-4827-bb1d-0c217d9985a5

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_ImportsBisAlt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_LiftFormNotMemBlowUpOf
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_aeval_blowUpSubst_liftForm_4b99591f2332


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
variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} {R : Type*} [CommRing R]
variable {J : Type}
namespace GroundTheory.Heights₂.Heights.NumbersDVR
theorem _root_.solution {P : Ideal (MRing ι R)} {u : J → MRing ι R} {p : MRing ι R}
    (h : p ∉ P) : liftForm (J := J) p ∉ blowUpOf P u := by
  rw [blowUpOf, RingHom.mem_ker, aeval_blowUpSubst_liftForm, Polynomial.C_eq_zero,
    Ideal.Quotient.eq_zero_iff_mem]
  exact h
end GroundTheory.Heights₂.Heights.NumbersDVR
