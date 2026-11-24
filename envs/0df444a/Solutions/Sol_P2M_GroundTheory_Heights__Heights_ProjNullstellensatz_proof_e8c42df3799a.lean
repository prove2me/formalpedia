-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ProjNullstellensatz_proof_e8c42df3799a
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:44:48.122344+00:00
-- url     : https://prove2.me/submissions/84027a79-f1ae-40a3-bc73-5a2e145faab6

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_PProjNullstellensatz

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
namespace GroundTheory.Heights₂.Heights
namespace ProjNullstellensatz
theorem _root_.solution (h₁ : FGNullstellensatz.Statement) :
    ProjNullstellensatz.Statement := by
  intro F _ n P hP
  have : P.IsPrime := hP.isPrime
  obtain ⟨j, hj⟩ := hP.isRelevant
  set D := MvPolynomial (Fin n) F ⧸ P
  have hr : Ideal.Quotient.mk P (X j) ≠ 0 := by
    rw [Ne, Ideal.Quotient.eq_zero_iff_mem]
    exact hj
  have hφ : ∃ φ : D →ₐ[F] AlgebraicClosure F, φ (Ideal.Quotient.mk P (X j)) ≠ 0 := by
    by_contra hne
    apply hr
    refine h₁ F D _ (fun φ => ?_)
    by_contra h
    exact hne ⟨φ, h⟩
  obtain ⟨φ, hφj⟩ := hφ
  have hcomp : φ.comp (Ideal.Quotient.mkₐ F P) = aeval (fun i => φ (Ideal.Quotient.mk P (X i))) := by
    apply MvPolynomial.algHom_ext
    intro i
    rw [AlgHom.comp_apply, aeval_X]
    rfl
  refine ⟨fun i => φ (Ideal.Quotient.mk P (X i)), ?_, ?_⟩
  · intro h0
    exact hφj (congrFun h0 j)
  · intro g hg
    rw [← hcomp, AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk,
      Ideal.Quotient.eq_zero_iff_mem.mpr hg, map_zero]
end ProjNullstellensatz
end GroundTheory.Heights₂.Heights
