-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ComplexSets_cone_isFiniteProjection_a2859d45cc1d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T04:28:49.669585+00:00
-- url     : https://prove2.me/submissions/a5ceabd7-09f2-499b-9006-b39cee113cb3

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_Statements
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ComplexSets_pullback_coneProj_e8e387377476
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ComplexSets_projHom_cone_X_abd38f0c6846

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.ComplexSets
open MvPolynomial Pointwise
noncomputable section
variable {n d : ℕ}
namespace GroundTheory.Heights₂.Heights.ComplexSets
theorem _root_.solution : IsFiniteProjection coneIdeal coneProj := by
  set φ := (projHom coneIdeal coneProj).toRingHom with hφ
  refine ⟨?_, ?_⟩
  · rw [injective_iff_map_eq_zero]
    intro P hP
    have hmem : pullback coneProj P ∈ coneIdeal := Ideal.Quotient.eq_zero_iff_mem.mp hP
    obtain ⟨q, hq⟩ := Ideal.mem_span_singleton'.mp hmem
    have h := congrArg (finSuccEquiv ℂ 2) hq
    rw [map_mul, finSuccEquiv_coneEq, pullback_coneProj] at h
    by_contra hP0
    have hq0 : finSuccEquiv ℂ 2 q ≠ 0 := by
      intro h0
      rw [h0, zero_mul] at h
      exact hP0 (Polynomial.C_eq_zero.mp h.symm)
    have hd := congrArg Polynomial.natDegree h
    rw [Polynomial.natDegree_C, Polynomial.natDegree_mul hq0
      (Polynomial.monic_X_pow_sub_C _ (by norm_num)).ne_zero, Polynomial.natDegree_X_pow_sub_C] at hd
    omega
  · rw [RingHom.finite_iff_isIntegral_and_finiteType]
    refine ⟨?_, ?_⟩
    · intro x
      obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
      induction p using MvPolynomial.induction_on with
      | C a =>
        have : Ideal.Quotient.mk coneIdeal (C a) = φ (C a) := by
          rw [hφ, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, projHom, AlgHom.comp_apply, pullback,
            aeval_C, Ideal.Quotient.mkₐ_eq_mk, MvPolynomial.algebraMap_eq]
        rw [this]
        exact RingHom.isIntegralElem_map φ
      | add p q hp hq =>
        rw [map_add]
        exact RingHom.IsIntegralElem.add φ hp hq
      | mul_X p i hp =>
        rw [map_mul]
        refine RingHom.IsIntegralElem.mul φ hp ?_
        fin_cases i
        · refine ⟨Polynomial.X ^ 2 - Polynomial.C (X 0 * X 1),
            Polynomial.monic_X_pow_sub_C _ (by norm_num), ?_⟩
          have e0 : φ (X 0) = Ideal.Quotient.mk coneIdeal (X 1) := projHom_cone_X 0
          have e1 : φ (X 1) = Ideal.Quotient.mk coneIdeal (X 2) := projHom_cone_X 1
          rw [Polynomial.eval₂_sub, Polynomial.eval₂_X_pow, Polynomial.eval₂_C, map_mul, e0, e1,
            ← map_pow, ← map_mul, ← map_sub, Ideal.Quotient.eq_zero_iff_mem]
          exact Ideal.subset_span rfl
        · have e : Ideal.Quotient.mk coneIdeal (X 1) = φ (X 0) := (projHom_cone_X 0).symm
          simp only [Fin.mk_one]
          rw [e]; exact RingHom.isIntegralElem_map φ
        · have e : Ideal.Quotient.mk coneIdeal (X 2) = φ (X 1) := (projHom_cone_X 1).symm
          rw [show ((⟨2, by norm_num⟩ : Fin 3)) = 2 from rfl, e]
          exact RingHom.isIntegralElem_map φ
    · have hc : φ.comp (algebraMap ℂ (MvPolynomial (Fin 2) ℂ)) =
          algebraMap ℂ (MvPolynomial (Fin 3) ℂ ⧸ coneIdeal) :=
        (projHom coneIdeal coneProj).comp_algebraMap
      refine RingHom.FiniteType.of_comp_finiteType (f := algebraMap ℂ (MvPolynomial (Fin 2) ℂ)) ?_
      rw [hc, RingHom.finiteType_algebraMap]
      infer_instance
end GroundTheory.Heights₂.Heights.ComplexSets
