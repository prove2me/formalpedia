-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FieldNumbers_ringKrullDim_sup_span_add_one_le_7d5f38d16890
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T03:54:06.771353+00:00
-- url     : https://prove2.me/submissions/25d1150d-a064-414d-8d60-acaf54de5b82

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsDegreeBound
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PHilbDegreeBound

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
variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} {F : Type u} [Field F]
attribute [local instance] MvPolynomial.weightedGradedAlgebra
omit [Fintype K] [DecidableEq K]
namespace GroundTheory.Heights₂.Heights.FieldNumbers
theorem _root_.solution {P : Ideal (MRing ι F)} [P.IsPrime] {s : MRing ι F}
    (hs : s ∉ P) :
    ringKrullDim (MRing ι F ⧸ (P ⊔ Ideal.span {s})) + 1 ≤ ringKrullDim (MRing ι F ⧸ P) := by
  refine ringKrullDim_succ_le_of_surjective (Ideal.Quotient.factor le_sup_left)
    (Ideal.Quotient.factor_surjective le_sup_left) (r := Ideal.Quotient.mk P s) ?_ ?_
  · exact mem_nonZeroDivisors_of_ne_zero (by rwa [Ne, Ideal.Quotient.eq_zero_iff_mem])
  · rw [Ideal.Quotient.factor_mk, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.mem_sup_right (Ideal.subset_span rfl)
end GroundTheory.Heights₂.Heights.FieldNumbers
