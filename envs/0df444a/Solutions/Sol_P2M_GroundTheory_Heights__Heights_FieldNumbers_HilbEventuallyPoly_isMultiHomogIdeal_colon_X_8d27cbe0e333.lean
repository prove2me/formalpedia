-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FieldNumbers_HilbEventuallyPoly_isMultiHomogIdeal_colon_X_8d27cbe0e333
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T04:27:13.438816+00:00
-- url     : https://prove2.me/submissions/4de5aced-4636-43cd-981d-b74f9d0bc5cc

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_HilbEventuallyPolyQualified
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_HilbEventuallyPoly_weightedHomogeneousComponent_mul_X_1e67a7f0ce90

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
namespace GroundTheory.Heights₂.Heights.FieldNumbers.HilbEventuallyPoly
theorem _root_.solution {I : Ideal (MRing ι F)} (hI : IsMultiHomogIdeal I)
    (v : Σ k, ι k) : IsMultiHomogIdeal (I.colon (Ideal.span {(X v : MRing ι F)})) := by
  intro f hf b
  rw [Submodule.mem_colon_span_singleton, smul_eq_mul] at hf ⊢
  rw [← weightedHomogeneousComponent_mul_X]
  exact hI _ hf _
end GroundTheory.Heights₂.Heights.FieldNumbers.HilbEventuallyPoly
