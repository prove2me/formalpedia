-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_newVar_not_mem_blowUpOf_60e69689759f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T04:42:57.596214+00:00
-- url     : https://prove2.me/submissions/7a0256c2-d410-482e-bfae-644d37d49e2e

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_ImportsBisAlt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_LiftFormNotMemBlowUpOf

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
theorem _root_.solution {P : Ideal (MRing ι R)} {u : J → MRing ι R} {j : J} (h : u j ∉ P) :
    (newVar j : MRing (extIdx ι J) R) ∉ blowUpOf P u := by
  rw [blowUpOf, RingHom.mem_ker, newVar, aeval_X]
  change ¬ (Polynomial.C (Ideal.Quotient.mk P (u j)) * Polynomial.X = 0)
  intro h0
  have h1 := congrArg (fun p => Polynomial.coeff p 1) h0
  simp only [Polynomial.coeff_C_mul_X, if_true, Polynomial.coeff_zero] at h1
  exact h (Ideal.Quotient.eq_zero_iff_mem.mp h1)
end GroundTheory.Heights₂.Heights.NumbersDVR
