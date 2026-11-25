-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FieldNumbers_smul_mk_monomial_649930483a0c
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T03:54:09.167617+00:00
-- url     : https://prove2.me/submissions/b2d4ba73-fe5d-45bf-baa2-00328fff2879

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PGradedFinite
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PIntNumBaseChange

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FieldNumbers
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR
noncomputable section
variable {K : Type*} [Fintype K] [DecidableEq K] {ι : K → Type*} [∀ k, Fintype (ι k)]
omit [Fintype K] [DecidableEq K] [∀ k, Fintype (ι k)]
namespace GroundTheory.Heights₂.Heights.FieldNumbers
theorem _root_.solution (E : Type*) [Field E] (J : Ideal (MRing ι E)) (d : (Σ k, ι k) →₀ ℕ)
    (c : E) : c • Ideal.Quotient.mk J (monomial d (1 : E)) = Ideal.Quotient.mk J (monomial d c) := by
  have h := map_smul (Ideal.Quotient.mkₐ E J) c (monomial d (1 : E))
  rw [smul_monomial, smul_eq_mul, mul_one, Ideal.Quotient.mkₐ_eq_mk] at h
  exact h.symm
end GroundTheory.Heights₂.Heights.FieldNumbers
