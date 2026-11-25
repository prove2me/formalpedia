-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FieldNumbers_blockMonomial_add_5a9f7ea51005
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T03:53:47.509272+00:00
-- url     : https://prove2.me/submissions/712e72c6-9156-4f08-bd17-5c1bdf52f4ae

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PGradedFinite
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PIntNumBase

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
universe u
variable {F : Type u} [Field F] {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type}
  [∀ k, Fintype (ι k)]
omit [DecidableEq K] [∀ k, Fintype (ι k)]
namespace GroundTheory.Heights₂.Heights.FieldNumbers
theorem _root_.solution (i : ∀ k, ι k) (m n : K → ℕ) :
    blockMonomial (F := F) i (m + n) = blockMonomial i m * blockMonomial i n := by
  simp [blockMonomial, pow_add, Finset.prod_mul_distrib]
end GroundTheory.Heights₂.Heights.FieldNumbers
