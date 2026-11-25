-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FieldNumbers_CutRegular_ringKrullDim_sup_span_add_one_le_6e63ac6fa7da
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T04:11:09.680826+00:00
-- url     : https://prove2.me/submissions/3031bebe-311f-4d1d-93be-27b24dbac0c1

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PHilbExactDivide
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PIntNumAdd
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_JacobianSmoothness_RingKrullDimLeRingKrullDimQuotientAddOne
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PCutRegular
import Theorems.Thm_GroundTheory_Arith_Abelian_Jacobian_ringKrullDim_quotient_add_one_le


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
open GroundTheory.Heights₂.Heights.FieldNumbers.CutRegular
variable {K : Type} [DecidableEq K] {ι : K → Type} {F : Type u} [Field F]
omit [DecidableEq K]
namespace GroundTheory.Heights₂.Heights.FieldNumbers.CutRegular
theorem _root_.solution {P : Ideal (MRing ι F)} [P.IsPrime] {s : MRing ι F}
    (hs : s ∉ P) :
    ringKrullDim (MRing ι F ⧸ (P ⊔ Ideal.span {s})) + 1 ≤ ringKrullDim (MRing ι F ⧸ P) := by
  have hne : (P ⊔ Ideal.span {s}).map (Ideal.Quotient.mk P) ≠ ⊥ := by
    intro h
    apply hs
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    have : Ideal.Quotient.mk P s ∈ (P ⊔ Ideal.span {s}).map (Ideal.Quotient.mk P) :=
      Ideal.mem_map_of_mem _ (Ideal.mem_sup_right (Ideal.mem_span_singleton_self s))
    rwa [h, Ideal.mem_bot] at this
  have := GroundTheory.Arith.Abelian.Jacobian.ringKrullDim_quotient_add_one_le _ hne
  rwa [ringKrullDim_eq_of_ringEquiv (DoubleQuot.quotQuotEquivQuotOfLE le_sup_left)] at this
end GroundTheory.Heights₂.Heights.FieldNumbers.CutRegular
