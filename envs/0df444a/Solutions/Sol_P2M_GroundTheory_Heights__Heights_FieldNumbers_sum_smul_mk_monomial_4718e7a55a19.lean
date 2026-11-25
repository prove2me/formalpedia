-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FieldNumbers_sum_smul_mk_monomial_4718e7a55a19
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T04:28:39.239582+00:00
-- url     : https://prove2.me/submissions/4895a65b-c95d-4a4e-8969-a81f690dc0c2

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PGradedFinite
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PIntNumBaseChange
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_smul_mk_monomial_649930483a0c

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
theorem _root_.solution (E : Type*) [Field E] (J : Ideal (MRing ι E)) {B : Type*} [Fintype B]
    (lift : B → (Σ k, ι k) →₀ ℕ) (c : B → E) :
    ∑ x, c x • Ideal.Quotient.mk J (monomial (lift x) (1 : E)) =
      Ideal.Quotient.mk J (∑ x, monomial (lift x) (c x)) := by
  rw [map_sum]
  exact Finset.sum_congr rfl fun x _ => smul_mk_monomial E J _ _
end GroundTheory.Heights₂.Heights.FieldNumbers
