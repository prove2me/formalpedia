-- Prove2me | solution 1 for WeierstrassCurve.ofResidualGaloisRep_residualGaloisRepOf_detIsCyclotomic
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/c24dd6b4-7a5d-503b-b15e-3fd9c9731574

import Definitions.Def_GaloisRep_LocalConditions
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
import Mathlib.RingTheory.RootsOfUnity.EnoughRootsOfUnity
import Theorems.Thm_WeierstrassCurve_apply_eq_pow_det_galoisRep_of_pow_eq_one
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_ofResidualGaloisRep_residualGaloisRepOf_detIsCyclotomic
p2m_attr_erase "instance" "WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral"
p2m_attr_erase "simp" "compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.Affine.mem_fibSet WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.placeOf_asIdeal"

open IsLocalRing Module Polynomial
open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point

namespace LCMazur

private theorem exists_isPrimitiveRoot (n : ℕ) [NeZero n] :
    ∃ ζ : AlgebraicClosure ℚ, IsPrimitiveRoot ζ n :=
  haveI : NeZero ((n : ℕ) : AlgebraicClosure ℚ) := ⟨Nat.cast_ne_zero.mpr (NeZero.ne n)⟩
  HasEnoughRootsOfUnity.exists_primitiveRoot (AlgebraicClosure ℚ) n

private theorem modEq_of_forall_apply_eq_pow (n : ℕ) [NeZero n]
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
    {a a' : ℕ} (ha : ∀ μ : AlgebraicClosure ℚ, μ ^ n = 1 → σ μ = μ ^ a)
    (ha' : ∀ μ : AlgebraicClosure ℚ, μ ^ n = 1 → σ μ = μ ^ a') : a ≡ a' [MOD n] := by
  obtain ⟨ζ, hζ⟩ := exists_isPrimitiveRoot n
  have h : ζ ^ a = ζ ^ a' := by rw [← ha ζ hζ.pow_eq_one, ha' ζ hζ.pow_eq_one]
  have hmod := (hζ.isOfFinOrder (NeZero.ne n)).pow_eq_pow_iff_modEq.mp h
  rwa [← hζ.eq_orderOf] at hmod

private theorem det_galoisRepModuleEnd_eq_natCast (W : WeierstrassCurve ℚ) (p : ℕ) [Fact p.Prime]
    (hΔ : W.Δ ≠ 0) (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) {a : ℕ}
    (ha : ∀ μ : AlgebraicClosure ℚ, μ ^ p = 1 → σ μ = μ ^ a) :
    LinearMap.det (galoisRepModuleEnd (K := AlgebraicClosure ℚ) ℚ W p σ) = (a : ZMod p) := by
  have hp : p.Prime := Fact.out
  haveI : W.IsElliptic := ⟨isUnit_iff_ne_zero.mpr hΔ⟩
  haveI : NeZero p := ⟨hp.ne_zero⟩
  have hpK : (p : AlgebraicClosure ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  have hmod : a ≡ (LinearMap.det ((DistribSMul.toAddMonoidHom
      (Submodule.torsionBy ℤ (W⁄(AlgebraicClosure ℚ)).Point p) σ).toZModLinearMap p)).val
      [MOD p] :=
    modEq_of_forall_apply_eq_pow p σ ha
      (fun ζ hζ => W.apply_eq_pow_det_galoisRep_of_pow_eq_one hp hpK σ ζ hζ)
  have hext : galoisRepModuleEnd (K := AlgebraicClosure ℚ) ℚ W p σ =
      (DistribSMul.toAddMonoidHom
        (Submodule.torsionBy ℤ (W⁄(AlgebraicClosure ℚ)).Point p) σ).toZModLinearMap p :=
    LinearMap.ext fun _ => rfl
  rw [hext, (ZMod.natCast_eq_natCast_iff _ _ _).mpr hmod, ZMod.natCast_zmod_val]

end LCMazur

theorem solution
    (W : WeierstrassCurve ℚ) (p : ℕ) [Fact p.Prime] (hΔ : W.Δ ≠ 0)
    (hcard : Nat.card (Submodule.torsionBy ℤ (W⁄(AlgebraicClosure ℚ)).Point p) = p ^ 2)
    (hker : GaloisFactorsThroughFiniteLevel
      (WeierstrassCurve.Affine.Point.galoisRepModuleEnd (K := AlgebraicClosure ℚ) ℚ W p)) :
    (GaloisRepAdic.ofResidualGaloisRep (W.residualGaloisRepOf p hcard hker)).DetIsCyclotomic p := by
  refine ⟨?_, fun n σ a ha => ?_⟩
  · rw [ZMod.natCast_self]
    exact Ideal.zero_mem _
  · rcases n with _ | n
    · rw [pow_zero, Nat.cast_one, Ideal.span_singleton_one]
      exact Submodule.mem_top
    · have ha' : ∀ μ : AlgebraicClosure ℚ, μ ^ p = 1 → σ μ = μ ^ a :=
        fun μ hμ => ha μ (by rw [pow_succ', pow_mul, hμ, one_pow])
      have h0 : LinearMap.det
          ((GaloisRepAdic.ofResidualGaloisRep (W.residualGaloisRepOf p hcard hker)).ρ σ) -
            (a : ZMod p) = 0 := by
        rw [sub_eq_zero]
        exact LCMazur.det_galoisRepModuleEnd_eq_natCast W p hΔ σ ha'
      rw [h0]
      exact Ideal.zero_mem _

end S_WeierstrassCurve_ofResidualGaloisRep_residualGaloisRepOf_detIsCyclotomic
end P2MW
export P2MW.S_WeierstrassCurve_ofResidualGaloisRep_residualGaloisRepOf_detIsCyclotomic (solution)
