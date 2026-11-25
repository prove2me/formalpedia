-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FieldNumbers_finiteDimensional_multiHomogForms_38c8ede14e27
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T03:53:58.530888+00:00
-- url     : https://prove2.me/submissions/f3741e4c-86df-41e8-a1e0-fe716e78a77d

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PGradedFinite
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_finite_monomials_of_multidegree_04d4ee134769

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
namespace GroundTheory.Heights₂.Heights.FieldNumbers
theorem _root_.solution (F : Type*) [Field F] (m : K → ℕ) :
    FiniteDimensional F (weightedHomogeneousSubmodule F (blockWeight ι) m) := by
  rw [weightedHomogeneousSubmodule_eq_finsupp_supported]
  have := (finite_monomials_of_multidegree (ι := ι) m).to_subtype
  exact Module.Finite.of_basis
    (basisRestrictSupport F {d | Finsupp.weight (blockWeight ι) d = m})
end GroundTheory.Heights₂.Heights.FieldNumbers
