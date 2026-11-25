-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_SectionComponents_exists_ringKrullDim_quotient_eq_187ebdf244d9
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T06:16:36.697177+00:00
-- url     : https://prove2.me/submissions/07bae0aa-6870-4396-8eb4-9bff2fbee9c5

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsSectionComponents
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_JacobianSmoothness_RingKrullDimLeRingKrullDimQuotientAddOne
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PSectionComponents
import Theorems.Thm_GroundTheory_Arith_Abelian_Jacobian_ringKrullDim_lt_top


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial
open GroundTheory.Heights₂.Heights.SectionComponents
variable {F : Type} [Field F] {n : ℕ}
namespace GroundTheory.Heights₂.Heights.SectionComponents
theorem _root_.solution (Q : Ideal (MvPolynomial (Fin n) F)) [Q.IsPrime] :
    ∃ m : ℕ, ringKrullDim (MvPolynomial (Fin n) F ⧸ Q) = m := by
  have _ : Algebra.FiniteType F (MvPolynomial (Fin n) F ⧸ Q) :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ F Q) (Ideal.Quotient.mkₐ_surjective F Q)
  have hlt := GroundTheory.Arith.Abelian.Jacobian.ringKrullDim_lt_top F
    (A := MvPolynomial (Fin n) F ⧸ Q)
  have hnn := ringKrullDim_nonneg_of_nontrivial (R := MvPolynomial (Fin n) F ⧸ Q)
  cases h : ringKrullDim (MvPolynomial (Fin n) F ⧸ Q) with
  | bot => rw [h] at hnn; exact absurd hnn (by simp)
  | coe y =>
    rw [h] at hlt
    have : y ≠ ⊤ := fun hy => by subst hy; exact lt_irrefl _ hlt
    obtain ⟨m, rfl⟩ := ENat.ne_top_iff_exists.mp this
    exact ⟨m, rfl⟩
end GroundTheory.Heights₂.Heights.SectionComponents
