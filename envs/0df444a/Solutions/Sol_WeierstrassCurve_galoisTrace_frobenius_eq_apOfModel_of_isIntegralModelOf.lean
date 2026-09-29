-- Prove2me | solution 1 for WeierstrassCurve.galoisTrace_frobenius_eq_apOfModel_of_isIntegralModelOf
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/566209c8-5f40-5b89-90d0-4a7ac20b6659

import Mathlib
import Definitions.Def_EllipticCurve_FrobeniusTrace
import Definitions.Def_FLTPrelim_Modularity
import Theorems.Thm_WeierstrassCurve_galoisTrace_frobenius_eq_apOfModel
import Theorems.Thm_WeierstrassCurve_exists_addEquiv_point_baseChange_variableChange_smul_algEquiv
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_galoisTrace_frobenius_eq_apOfModel_of_isIntegralModelOf
p2m_attr_erase "instance" "WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly"
p2m_attr_erase "simp" "FrobeniusEndo.linePencil_apply compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.Universal.halveX_zero WeierstrassCurve.Universal.specialize_X_one WeierstrassCurve.Universal.coeff_halve WeierstrassCurve.Universal.specialize_X_two WeierstrassCurve.Universal.halveCoeff_zero WeierstrassCurve.Universal.specialize_X_four"
p2m_attr_erase "simp" "WeierstrassCurve.Universal.coeff_halveX WeierstrassCurve.Universal.specialize_X_three WeierstrassCurve.Universal.specialize_X_zero"

open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point

namespace W4A_F2A_TRANSPORT

open scoped WeierstrassCurve.Affine

universe u v

variable {F : Type u} {K : Type v} [Field F] [Field K] [DecidableEq K] [Algebra F K]

noncomputable def torsionByCongr {M N : Type*} [AddCommGroup M] [AddCommGroup N]
    (φ : M ≃+ N) (n : ℕ) :
    Submodule.torsionBy ℤ M n ≃+ Submodule.torsionBy ℤ N n where
  toFun x := ⟨φ x, by
    have hx := x.2
    rw [Submodule.mem_torsionBy_iff] at hx ⊢
    rw [← map_zsmul φ, hx, _root_.map_zero]⟩
  invFun y := ⟨φ.symm y, by
    have hy := y.2
    rw [Submodule.mem_torsionBy_iff] at hy ⊢
    rw [← map_zsmul φ.symm, hy, _root_.map_zero]⟩
  left_inv x := Subtype.ext (φ.symm_apply_apply x)
  right_inv y := Subtype.ext (φ.apply_symm_apply y)
  map_add' x y := Subtype.ext (map_add φ (x : M) (y : M))

@[scoped simp] lemma coe_torsionByCongr_apply {M N : Type*} [AddCommGroup M] [AddCommGroup N]
    (φ : M ≃+ N) (n : ℕ) (x : Submodule.torsionBy ℤ M n) :
    ((torsionByCongr φ n x : Submodule.torsionBy ℤ N n) : N) = φ x := rfl

@[scoped simp] lemma coe_torsionByCongr_symm_apply {M N : Type*} [AddCommGroup M] [AddCommGroup N]
    (φ : M ≃+ N) (n : ℕ) (y : Submodule.torsionBy ℤ N n) :
    (((torsionByCongr φ n).symm y : Submodule.torsionBy ℤ M n) : M) = φ.symm y := rfl

noncomputable def torsionLinearEquiv (E₁ E₂ : WeierstrassCurve F) (n : ℕ)
    (φ : (E₁.baseChange K).toAffine.Point ≃+ (E₂.baseChange K).toAffine.Point) :
    Submodule.torsionBy ℤ (E₁.baseChange K).toAffine.Point n ≃ₗ[ZMod n]
      Submodule.torsionBy ℤ (E₂.baseChange K).toAffine.Point n :=
  { (torsionByCongr φ n).toAddMonoidHom.toZModLinearMap n with
    invFun := (torsionByCongr φ n).symm
    left_inv := (torsionByCongr φ n).left_inv
    right_inv := (torsionByCongr φ n).right_inv }

@[scoped simp] lemma coe_torsionLinearEquiv_apply (E₁ E₂ : WeierstrassCurve F) (n : ℕ)
    (φ : (E₁.baseChange K).toAffine.Point ≃+ (E₂.baseChange K).toAffine.Point)
    (x : Submodule.torsionBy ℤ (E₁.baseChange K).toAffine.Point n) :
    ((torsionLinearEquiv E₁ E₂ n φ x : Submodule.torsionBy ℤ (E₂.baseChange K).toAffine.Point n) :
      (E₂.baseChange K).toAffine.Point) = φ x := rfl

@[scoped simp] lemma coe_torsionLinearEquiv_symm_apply (E₁ E₂ : WeierstrassCurve F) (n : ℕ)
    (φ : (E₁.baseChange K).toAffine.Point ≃+ (E₂.baseChange K).toAffine.Point)
    (y : Submodule.torsionBy ℤ (E₂.baseChange K).toAffine.Point n) :
    (((torsionLinearEquiv E₁ E₂ n φ).symm y :
        Submodule.torsionBy ℤ (E₁.baseChange K).toAffine.Point n) :
      (E₁.baseChange K).toAffine.Point) = φ.symm y := rfl

lemma galoisRepModuleEnd_eq_conj (E₁ E₂ : WeierstrassCurve F) (n : ℕ)
    (φ : (E₁.baseChange K).toAffine.Point ≃+ (E₂.baseChange K).toAffine.Point)
    (σ : K ≃ₐ[F] K)
    (hφ : ∀ P : (E₁.baseChange K).toAffine.Point, φ (σ • P) = σ • φ P) :
    galoisRepModuleEnd (K := K) F E₂ n σ =
      (torsionLinearEquiv E₁ E₂ n φ).conj (galoisRepModuleEnd (K := K) F E₁ n σ) := by
  apply LinearMap.ext
  intro y
  apply Subtype.ext
  rw [LinearEquiv.conj_apply, LinearMap.comp_apply, LinearMap.comp_apply,
    LinearEquiv.coe_coe, LinearEquiv.coe_coe, coe_torsionLinearEquiv_apply,
    galoisRepModuleEnd_apply, galoisRepModuleEnd_apply]

  change σ • (y : (E₂.baseChange K).toAffine.Point) =
    φ (σ • (((torsionLinearEquiv E₁ E₂ n φ).symm y :
        Submodule.torsionBy ℤ (E₁.baseChange K).toAffine.Point n) :
      (E₁.baseChange K).toAffine.Point))
  rw [hφ, coe_torsionLinearEquiv_symm_apply, AddEquiv.apply_symm_apply]

theorem galoisTrace_eq_of_addEquiv (E₁ E₂ : WeierstrassCurve F) (n : ℕ)
    (φ : (E₁.baseChange K).toAffine.Point ≃+ (E₂.baseChange K).toAffine.Point)
    (σ : K ≃ₐ[F] K)
    (hφ : ∀ P : (E₁.baseChange K).toAffine.Point, φ (σ • P) = σ • φ P) :
    galoisTrace (K := K) F E₁ n σ = galoisTrace (K := K) F E₂ n σ := by
  rw [galoisTrace_def, galoisTrace_def, galoisRepModuleEnd_eq_conj E₁ E₂ n φ σ hφ,
    LinearMap.trace_conj']

theorem galoisTrace_variableChange (E : WeierstrassCurve F) (C : VariableChange F) (n : ℕ)
    (σ : K ≃ₐ[F] K) :
    galoisTrace (K := K) F (C • E) n σ = galoisTrace (K := K) F E n σ := by
  obtain ⟨φ, hφ⟩ :=
    WeierstrassCurve.exists_addEquiv_point_baseChange_variableChange_smul_algEquiv (K := K) E C
  exact galoisTrace_eq_of_addEquiv (C • E) E n φ σ (hφ σ)

end W4A_F2A_TRANSPORT
p2m_reactivate "P2MW.S_WeierstrassCurve_galoisTrace_frobenius_eq_apOfModel_of_isIntegralModelOf.W4A_F2A_TRANSPORT"

theorem solution
    (E : WeierstrassCurve ℚ) [E.IsElliptic] {W : WeierstrassCurve ℤ} (hW : W.IsIntegralModelOf E)
    {p ℓ : ℕ} (hp : p.Prime) (hℓ : ℓ.Prime) (hgood : W.IsGoodPrimeFor ℓ) (hℓp : ℓ ≠ p)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime ℓ)
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (hσ : A.IsFrobeniusAt σ ℓ) :
    galoisTrace (K := AlgebraicClosure ℚ) ℚ E p σ = ((W.apOfModel ℓ : ℤ) : ZMod p) := by
  obtain ⟨C, hC⟩ := hW
  have key := WeierstrassCurve.galoisTrace_frobenius_eq_apOfModel W p ℓ hp hℓ hℓp hgood A hA σ hσ
  rw [← hC, W4A_F2A_TRANSPORT.galoisTrace_variableChange (K := AlgebraicClosure ℚ) E C p σ] at key
  exact key

end S_WeierstrassCurve_galoisTrace_frobenius_eq_apOfModel_of_isIntegralModelOf
end P2MW
export P2MW.S_WeierstrassCurve_galoisTrace_frobenius_eq_apOfModel_of_isIntegralModelOf (solution)
