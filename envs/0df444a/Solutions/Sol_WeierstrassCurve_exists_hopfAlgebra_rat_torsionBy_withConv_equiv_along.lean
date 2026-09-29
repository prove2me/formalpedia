-- Prove2me | solution 1 for WeierstrassCurve.exists_hopfAlgebra_rat_torsionBy_withConv_equiv_along
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/aba23775-6d78-5150-aa44-5f815bb8bfcd

import Mathlib
import Definitions.Def_GaloisRep_Flat
import Definitions.Def_FLTPrelim_GaloisRep
import Definitions.Def_FLTPrelim_Modularity
import Theorems.Thm_WeierstrassCurve_exists_hopfAlgebra_rat_torsionBy_withConv_equiv
import Theorems.Thm_WeierstrassCurve_exists_isIntegralModelOf_rat
import Theorems.Thm_WeierstrassCurve_exists_variableChange_map_intCast_padic_eq_map_along
import Theorems.Thm_WeierstrassCurve_exists_linearEquiv_torsionBy_of_variableChange_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_exists_hopfAlgebra_rat_torsionBy_withConv_equiv_along
p2m_attr_erase "instance" "HomogeneousIdealQuotientGrading.quotGradingSubmoduleGradedMonoid HomogeneousIdealQuotientGrading.quotGradingGradedMonoid HomogeneousIdealQuotientGrading.quotGradingSubmoduleGradedAlgebraOfHomogeneous HomogeneousIdealQuotientGrading.quotGradingGradedRingOfHomogeneous WeierstrassProjModel.quotGradingSubmoduleDegreeZeroFiniteType WeierstrassProjModel.kw_lrChart_tensorCommRing WeierstrassProjModel.kw_lrChart_biGrading_gradedAlgebra WeierstrassProjModel.projModel_isIso_spec_mapCR WeierstrassProjModel.kw_lrSymOC_isDomain_ℬ₀ WeierstrassProjModel.isProper_projModelStrCR WeierstrassProjModel.homogeneousSubmoduleDegreeZeroFiniteType WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly"
p2m_attr_erase "simp" "WeierstrassProjModel.schemeHomOverComp_coe WeierstrassProjModel.RelativeGroupLaw.mk.sizeOf_spec WeierstrassProjModel.RelativeGroupLaw.nsmul_zero WeierstrassProjModel.RelativeGroupLaw.nsmul_succ WeierstrassProjModel.projModelHomogeneousIdealCR_toIdeal WeierstrassProjModel.RelativeGroupLaw.mk.injEq WeierstrassProjModel.RelativeGroupLaw.mem_torsionSubset HomogeneousIdealQuotientGrading.pieceHom_coe HomogeneousIdealQuotientGrading.quotDecompose_mk HomogeneousIdealQuotientGrading.quotGradingPieceHom_coe NeronModelInfra.specGenericFibreInclusion_eq NeronModelInfra.genericFibreRestrict_coe_comp_snd NeronModelInfra.genericFibreRestrict_coe_comp_fst WeierstrassProjModel.kw_lrAdd_substHom_X WeierstrassProjModel.kw_lrSym_substHom_X compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec"
p2m_attr_erase "simp" "WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.Affine.vcY_vcYInv WeierstrassCurve.Affine.vcXInv_vcX WeierstrassCurve.Affine.Point.vcFun_zero WeierstrassCurve.Affine.vcX_vcXInv WeierstrassCurve.Affine.vcYInv_vcY WeierstrassCurve.Affine.Point.vcInvFun_zero WeierstrassCurve.Universal.halveX_zero WeierstrassCurve.Universal.specialize_X_one WeierstrassCurve.Universal.coeff_halve WeierstrassCurve.Universal.specialize_X_two WeierstrassCurve.Universal.halveCoeff_zero WeierstrassCurve.Universal.specialize_X_four WeierstrassCurve.Universal.coeff_halveX WeierstrassCurve.Universal.specialize_X_three WeierstrassCurve.Universal.specialize_X_zero"

set_option maxHeartbeats 3200000

open scoped WeierstrassCurve.Affine in
open WeierstrassCurve WeierstrassCurve.Affine.Point in
theorem solution
    (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Algebra R ℚ] [IsFractionRing R ℚ]
    (E : WeierstrassCurve ℚ) (W₀ : WeierstrassCurve R) (heq : W₀⁄ℚ = E)
    (p : ℕ) [Fact p.Prime]
    (f : R →+* ℤ_[p])
    (hfc : ∀ r : R, ((f r : ℤ_[p]) : ℚ_[p]) = (algebraMap ℚ ℚ_[p]) (algebraMap R ℚ r)) :
    letI : DecidableEq (AlgebraicClosure ℚ) := Classical.decEq _
    letI : DecidableEq (AlgebraicClosure ℚ_[p]) := Classical.decEq _
    ∃ (A : Type) (_ : CommRing A) (_ : HopfAlgebra ℚ A),
      Module.Finite ℚ A ∧ Coalgebra.IsCocomm ℚ A ∧
      (∃ eA : WithConv (A →ₐ[ℚ] AlgebraicClosure ℚ) ≃
            Submodule.torsionBy ℤ (E⁄(AlgebraicClosure ℚ)).Point p,
        (∀ f g, eA (f * g) = eA f + eA g) ∧
        ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
          (f g : WithConv (A →ₐ[ℚ] AlgebraicClosure ℚ)),
          (∀ a : A, g a = σ (f a)) → eA g = σ • (eA f)) ∧
      (∃ eAp : WithConv (A →ₐ[ℚ] AlgebraicClosure ℚ_[p]) ≃
            Submodule.torsionBy ℤ (((W₀.map f)⁄ℚ_[p])⁄(AlgebraicClosure ℚ_[p])).Point p,
        (∀ f g, eAp (f * g) = eAp f + eAp g) ∧
        ∀ (σ : AlgebraicClosure ℚ_[p] ≃ₐ[ℚ_[p]] AlgebraicClosure ℚ_[p])
          (f g : WithConv (A →ₐ[ℚ] AlgebraicClosure ℚ_[p])),
          (∀ a : A, g a = σ (f a)) → eAp g = σ • (eAp f)) := by
  letI : DecidableEq (AlgebraicClosure ℚ) := Classical.decEq _
  letI : DecidableEq (AlgebraicClosure ℚ_[p]) := Classical.decEq _
  obtain ⟨W, hW⟩ := WeierstrassCurve.exists_isIntegralModelOf_rat E
  obtain ⟨A, _, _, hAfin, hAcocomm, ⟨eA, heA_add, heA_act⟩, ⟨eAp', heAp'_add, heAp'_act⟩⟩ :=
    WeierstrassCurve.exists_hopfAlgebra_rat_torsionBy_withConv_equiv E hW p
  obtain ⟨C, hC⟩ :=
    WeierstrassCurve.exists_variableChange_map_intCast_padic_eq_map_along R E W₀ heq hW p f hfc
  obtain ⟨φ, hφ⟩ :=
    WeierstrassCurve.exists_linearEquiv_torsionBy_of_variableChange_eq
      (F := ℚ_[p]) (AlgebraicClosure ℚ_[p]) C hC p
  refine ⟨A, _, _, hAfin, hAcocomm, ⟨eA, heA_add, heA_act⟩, ?_⟩

  refine ⟨eAp'.trans φ.toEquiv.symm, ?_, ?_⟩
  · intro g₁ g₂
    show φ.symm (eAp' (g₁ * g₂)) = φ.symm (eAp' g₁) + φ.symm (eAp' g₂)
    rw [heAp'_add]
    exact φ.symm.map_add _ _
  · intro σ g₁ g₂ hgσ
    show φ.symm (eAp' g₂) = σ • φ.symm (eAp' g₁)
    rw [heAp'_act σ g₁ g₂ hgσ]
    have : ∀ y, φ.symm (σ • y) = σ • φ.symm y := fun y => by
      apply φ.injective
      rw [LinearEquiv.apply_symm_apply, hφ, LinearEquiv.apply_symm_apply]
    exact this _

end S_WeierstrassCurve_exists_hopfAlgebra_rat_torsionBy_withConv_equiv_along
end P2MW
export P2MW.S_WeierstrassCurve_exists_hopfAlgebra_rat_torsionBy_withConv_equiv_along (solution)
