-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_mem_blowUpOf_of_sub_30a04624d21b
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:37:13.955469+00:00
-- url     : https://prove2.me/submissions/2cce5a75-7941-42ce-84f1-9f31cf767cc7

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
theorem _root_.solution {P : Ideal (MRing ι R)} {u : J → MRing ι R} {j j' : J}
    {a a' : MRing ι R} (h : u j * a - u j' * a' ∈ P) :
    newVar j * liftForm a - newVar j' * liftForm a' ∈ blowUpOf P u := by
  rw [blowUpOf, RingHom.mem_ker]
  simp only [map_sub, map_mul, newVar, aeval_X, blowUpSubst, aeval_blowUpSubst_liftForm]
  have e : Polynomial.C (Ideal.Quotient.mk P (u j)) * Polynomial.X * Polynomial.C (Ideal.Quotient.mk P a) -
      Polynomial.C (Ideal.Quotient.mk P (u j')) * Polynomial.X * Polynomial.C (Ideal.Quotient.mk P a') =
      Polynomial.C (Ideal.Quotient.mk P (u j * a - u j' * a')) * Polynomial.X := by
    simp only [map_sub, map_mul]; ring
  rw [e, Ideal.Quotient.eq_zero_iff_mem.mpr h, map_zero, zero_mul]
end GroundTheory.Heights₂.Heights.NumbersDVR
