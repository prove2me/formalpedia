-- Prove2me | solution 1 for WeierstrassCurve.galoisTrace_complexConjugation_eq_zero_and_det_eq_neg_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/4e1a427f-630d-5251-83a2-8479cd404de8

import Mathlib
import Definitions.Def_EllipticCurve_FrobeniusTrace
import Definitions.Def_GaloisRep_ComplexConjugation
import Theorems.Thm_WeierstrassCurve_det_galoisRep_eq_neg_one_of_mul_self_eq_one
import Theorems.Thm_WeierstrassCurve_finrank_torsionBy_of_isAlgClosed
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_galoisTrace_complexConjugation_eq_zero_and_det_eq_neg_one
p2m_attr_erase "instance" "WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral"
p2m_attr_erase "simp" "compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.Affine.mem_fibSet WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.placeOf_asIdeal"

set_option autoImplicit false

open WeierstrassCurve WeierstrassCurve.Affine.Point

namespace P2mWs11A2

theorem matrix_trace_eq_zero {R : Type*} [CommRing R] [IsDomain R] (A : Matrix (Fin 2) (Fin 2) R)
    (hA : A * A = 1) (hdet : A.det = -1) : A.trace = 0 := by
  have h00 := congrFun (congrFun hA 0) 0
  have h01 := congrFun (congrFun hA 0) 1
  have h10 := congrFun (congrFun hA 1) 0
  have h11 := congrFun (congrFun hA 1) 1
  simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply_eq, Matrix.one_apply_ne, ne_eq,
    zero_ne_one, one_ne_zero, not_false_eq_true, Fin.isValue] at h00 h01 h10 h11
  rw [Matrix.det_fin_two] at hdet
  rw [Matrix.trace_fin_two]
  by_contra ht

  have h01' : A 0 1 = 0 := by
    have : A 0 1 * (A 0 0 + A 1 1) = 0 := by linear_combination h01
    exact (mul_eq_zero.mp this).resolve_right ht
  have h10' : A 1 0 = 0 := by
    have : A 1 0 * (A 0 0 + A 1 1) = 0 := by linear_combination h10
    exact (mul_eq_zero.mp this).resolve_right ht

  have e1 : A 0 0 * A 0 0 = 1 := by rw [h01'] at h00; linear_combination h00
  have e3 : A 0 0 * A 1 1 = -1 := by rw [h01', h10'] at hdet; linear_combination hdet
  apply ht
  have : A 0 0 * (A 0 0 + A 1 1) = 0 := by linear_combination e1 + e3
  rcases mul_eq_zero.mp this with h | h
  · exfalso; rw [h, zero_mul] at e1; exact zero_ne_one e1
  · exact h

theorem trace_eq_zero_of_mul_self_eq_one {k : Type*} [Field k] {V : Type*} [AddCommGroup V] [Module k V]
    (h2 : Module.finrank k V = 2) (f : Module.End k V) (hf : f * f = 1) (hdet : LinearMap.det f = -1) :
    LinearMap.trace k V f = 0 := by
  classical
  have : FiniteDimensional k V := .of_finrank_pos (by omega)
  let b : Module.Basis (Fin 2) k V := Module.finBasisOfFinrankEq k V h2
  rw [LinearMap.trace_eq_matrix_trace k b]
  apply matrix_trace_eq_zero
  · rw [← LinearMap.toMatrix_mul, hf, LinearMap.toMatrix_one]
  · rw [LinearMap.det_toMatrix b, hdet]

theorem complexConjugation_ne_one : complexConjugation ≠ 1 := by
  intro h
  obtain ⟨x, hx⟩ : ∃ x : AlgebraicClosure ℚ, x * x = -1 := by
    obtain ⟨x, hx⟩ := IsAlgClosed.exists_pow_nat_eq (-1 : AlgebraicClosure ℚ) (n := 2) (by norm_num)
    exact ⟨x, by rw [← sq]; exact hx⟩
  have hfix : complexConjugation x = x := by rw [h, AlgEquiv.one_apply]
  have hconj : starRingEnd ℂ (complexEmbedding x) = complexEmbedding x := by
    rw [← complexEmbedding_complexConjugation, hfix]
  have hz : complexEmbedding x * complexEmbedding x = -1 := by rw [← map_mul, hx, map_neg, map_one]
  have hns : complexEmbedding x * complexEmbedding x = (Complex.normSq (complexEmbedding x) : ℂ) := by
    have h0 := Complex.mul_conj (complexEmbedding x)
    rw [hconj] at h0
    exact h0
  have hre := congrArg Complex.re (hz.symm.trans hns)
  simp only [Complex.neg_re, Complex.one_re, Complex.ofReal_re] at hre
  linarith [Complex.normSq_nonneg (complexEmbedding x)]

end P2mWs11A2

open P2mWs11A2 in
theorem solution [DecidableEq (AlgebraicClosure ℚ)]
    (W : WeierstrassCurve ℚ) [W.IsElliptic] {p : ℕ} (hp : p.Prime) :
    WeierstrassCurve.Affine.Point.galoisTrace (K := AlgebraicClosure ℚ) ℚ W p complexConjugation = 0 ∧
      LinearMap.det (WeierstrassCurve.Affine.Point.galoisRepModuleEnd (K := AlgebraicClosure ℚ) ℚ W p
        complexConjugation) = -1 := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hdet : LinearMap.det (galoisRepModuleEnd (K := AlgebraicClosure ℚ) ℚ W p complexConjugation) = -1 :=
    WeierstrassCurve.det_galoisRep_eq_neg_one_of_mul_self_eq_one W hp complexConjugation
      complexConjugation_mul_self complexConjugation_ne_one
  refine ⟨?_, hdet⟩
  have hp0 : ((p : ℕ) : AlgebraicClosure ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have h2 := WeierstrassCurve.finrank_torsionBy_of_isAlgClosed (F := ℚ) (K := AlgebraicClosure ℚ) W (p := p) hp0
  rw [galoisTrace_def]
  refine trace_eq_zero_of_mul_self_eq_one h2 _ ?_ hdet
  rw [← map_mul, complexConjugation_mul_self, map_one]

end S_WeierstrassCurve_galoisTrace_complexConjugation_eq_zero_and_det_eq_neg_one
end P2MW
export P2MW.S_WeierstrassCurve_galoisTrace_complexConjugation_eq_zero_and_det_eq_neg_one (solution)
