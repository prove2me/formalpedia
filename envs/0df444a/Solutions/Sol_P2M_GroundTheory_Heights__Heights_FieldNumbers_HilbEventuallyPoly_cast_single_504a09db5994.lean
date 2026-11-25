-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FieldNumbers_HilbEventuallyPoly_cast_single_504a09db5994
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T03:53:10.330266+00:00
-- url     : https://prove2.me/submissions/59e4c7b2-634c-4511-9464-99ada50124c5

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_HilbEventuallyPolyQualified

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
open GroundTheory.Heights₂.Heights.FieldNumbers.HilbEventuallyPoly
variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} {F : Type*} [Field F]
attribute [local instance] MvPolynomial.weightedGradedAlgebra
omit [Fintype K]
namespace GroundTheory.Heights₂.Heights.FieldNumbers.HilbEventuallyPoly
theorem _root_.solution (k : K) :
    (fun k' => (((Pi.single k 1 : K → ℕ) k' : ℕ) : ℤ)) = Pi.single k 1 := by
  funext k'
  by_cases h : k' = k
  · subst h; simp
  · simp [h]
end GroundTheory.Heights₂.Heights.FieldNumbers.HilbEventuallyPoly
