-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FieldNumbers_HilbEventuallyPoly_isMultiHomogIdeal_sup_span_e78dfa2b1c24
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T04:30:38.142976+00:00
-- url     : https://prove2.me/submissions/102fbca7-2232-4b6d-a67a-aa9f2bb85247

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_HilbEventuallyPolyQualified
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_HilbEventuallyPoly_isMultiHomogIdeal_iff_isHomogeneous_6c97bf347823

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
    {s : MRing ι F} {c : K → ℕ} (hs : IsMultiHomog s c) :
    IsMultiHomogIdeal (I ⊔ Ideal.span {s}) := by
  rw [isMultiHomogIdeal_iff_isHomogeneous] at hI ⊢
  refine hI.sup (Ideal.homogeneous_span _ _ ?_)
  intro x hx
  rw [Set.mem_singleton_iff] at hx
  subst hx
  exact ⟨c, hs⟩
end GroundTheory.Heights₂.Heights.FieldNumbers.HilbEventuallyPoly
