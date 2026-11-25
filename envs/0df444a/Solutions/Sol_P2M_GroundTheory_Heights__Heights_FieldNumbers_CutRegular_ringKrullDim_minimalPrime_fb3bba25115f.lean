-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FieldNumbers_CutRegular_ringKrullDim_minimalPrime_fb3bba25115f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T08:19:04.637974+00:00
-- url     : https://prove2.me/submissions/198d15fa-ef1c-4328-ba45-8c78c3bbf8ea

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PHilbExactDivide
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PIntNumAdd
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_JacobianSmoothness_RingKrullDimLeRingKrullDimQuotientAddOne
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PCutRegular
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_CutRegular_eq_of_add_one_le_of_le_9a68ecf72589
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_CutRegular_le_of_height_add_0297706b95e3
import Theorems.Thm_GroundTheory_Arith_Abelian_Jacobian_height_add_ringKrullDim_quotient
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
namespace GroundTheory.Heights₂.Heights.FieldNumbers.CutRegular
theorem _root_.solution [Fintype K] [∀ k, Fintype (ι k)] {P W : Ideal (MRing ι F)}
    [P.IsPrime] {s : MRing ι F} (hs : s ∉ P) (hW : W ∈ (P ⊔ Ideal.span {s}).minimalPrimes)
    {e : ℕ} (hdim : ringKrullDim (MRing ι F ⧸ P) = ((e + 1 : ℕ) : WithBot ℕ∞)) :
    ringKrullDim (MRing ι F ⧸ W) = ((e : ℕ) : WithBot ℕ∞) := by
  have hWprime : W.IsPrime := hW.1.1
  have hPW : P ≤ W := le_sup_left.trans hW.1.2
  have hsW : s ∈ W := (le_sup_right.trans hW.1.2) (Ideal.mem_span_singleton_self _)
  have _ : Algebra.FiniteType F (MRing ι F ⧸ P) :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ F P) (Ideal.Quotient.mkₐ_surjective F P)
  set W' : Ideal (MRing ι F ⧸ P) := W.map (Ideal.Quotient.mk P)
  have _ : W'.IsPrime :=
    Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (by rwa [Ideal.mk_ker])
  have hW'ne : W' ≠ ⊥ := by
    intro h
    apply hs
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    have : Ideal.Quotient.mk P s ∈ W' := Ideal.mem_map_of_mem _ hsW
    rwa [h, Ideal.mem_bot] at this
  have hht : W'.height ≤ 1 := Ideal.map_height_le_one_of_mem_minimalPrimes hW
  have hquot : ringKrullDim ((MRing ι F ⧸ P) ⧸ W') = ringKrullDim (MRing ι F ⧸ W) :=
    ringKrullDim_eq_of_ringEquiv (DoubleQuot.quotQuotEquivQuotOfLE hPW)
  have hform := GroundTheory.Arith.Abelian.Jacobian.height_add_ringKrullDim_quotient F W'
  have hdrop := GroundTheory.Arith.Abelian.Jacobian.ringKrullDim_quotient_add_one_le W' hW'ne
  rw [hquot, hdim] at hform hdrop
  exact eq_of_add_one_le_of_le hdrop (le_of_height_add hht hform)
end GroundTheory.Heights₂.Heights.FieldNumbers.CutRegular
