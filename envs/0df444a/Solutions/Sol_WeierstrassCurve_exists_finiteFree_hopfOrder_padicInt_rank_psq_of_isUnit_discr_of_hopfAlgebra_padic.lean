-- Prove2me | solution 1 for WeierstrassCurve.exists_finiteFree_hopfOrder_padicInt_rank_psq_of_isUnit_discr_of_hopfAlgebra_padic
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/a21a36ee-4cce-5d55-8ea3-9e6cb0ed7c1f

import Mathlib
import Definitions.Def_GaloisRep_Flat
import Theorems.Thm_AlgHom_liftEquiv_symm_withConv_mul
import Theorems.Thm_WeierstrassCurve_exists_finiteFree_hopfAlgebra_padicInt_torsionBy_rank_psq_of_isUnit_discr
import Theorems.Thm_HopfAlgebra_exists_algEquiv_comul_of_withConv_equiv_algClosure_padic
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_exists_finiteFree_hopfOrder_padicInt_rank_psq_of_isUnit_discr_of_hopfAlgebra_padic
p2m_attr_erase "instance" "HomogeneousIdealQuotientGrading.quotGradingSubmoduleGradedMonoid HomogeneousIdealQuotientGrading.quotGradingGradedMonoid HomogeneousIdealQuotientGrading.quotGradingSubmoduleGradedAlgebraOfHomogeneous HomogeneousIdealQuotientGrading.quotGradingGradedRingOfHomogeneous WeierstrassProjModel.quotGradingSubmoduleDegreeZeroFiniteType WeierstrassProjModel.kw_lrChart_tensorCommRing WeierstrassProjModel.kw_lrChart_biGrading_gradedAlgebra WeierstrassProjModel.projModel_isIso_spec_mapCR WeierstrassProjModel.kw_lrSymOC_isDomain_ℬ₀ WeierstrassProjModel.isProper_projModelStrCR WeierstrassProjModel.homogeneousSubmoduleDegreeZeroFiniteType AlgebraicCurve.Place.instIsScalarTowerSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Divisor.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instSMulAlgEquiv AlgebraicCurve.Place.instIsPrincipalIdealRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instIsDiscreteValuationRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Pic0.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instAlgebraSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instMulActionAlgEquiv AlgebraicCurve.Pic0.instSMulAlgEquiv AlgebraicCurve.CurveModel.isProper AlgebraicCurve.CurveModel.isIntegral AlgebraicCurve.CurveModel.smooth WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly"
p2m_attr_erase "simp" "WeierstrassProjModel.schemeHomOverComp_coe WeierstrassProjModel.RelativeGroupLaw.mk.sizeOf_spec WeierstrassProjModel.RelativeGroupLaw.nsmul_zero WeierstrassProjModel.RelativeGroupLaw.nsmul_succ WeierstrassProjModel.projModelHomogeneousIdealCR_toIdeal WeierstrassProjModel.RelativeGroupLaw.mk.injEq WeierstrassProjModel.RelativeGroupLaw.mem_torsionSubset HomogeneousIdealQuotientGrading.pieceHom_coe HomogeneousIdealQuotientGrading.quotDecompose_mk HomogeneousIdealQuotientGrading.quotGradingPieceHom_coe NeronModelInfra.specGenericFibreInclusion_eq NeronModelInfra.genericFibreRestrict_coe_comp_snd NeronModelInfra.genericFibreRestrict_coe_comp_fst WeierstrassProjModel.kw_lrAdd_substHom_X WeierstrassProjModel.kw_lrSym_substHom_X WeierstrassProjModel.kw_lrThird_substHom_X AlgebraicGeometry.schemeFibreEndo_snd AlgebraicGeometry.schemeFibreEndo_fst AlgebraicCurve.Place.mk.injEq AlgebraicCurve.Divisor.degree_single AlgebraicCurve.Divisor.smul_single AlgebraicCurve.Place.smul_toValuationSubring AlgebraicCurve.Place.heightOneSpectrum_asIdeal AlgebraicCurve.Place.coe_algebraMap AlgebraicCurve.Place.ord_one AlgebraicCurve.Place.coe_smulRingEquiv_apply AlgebraicCurve.Pic0.coe_degZeroSMulHom AlgebraicCurve.Place.deg_smul AlgebraicCurve.Pic0.mk_zero AlgebraicCurve.Place.mk.sizeOf_spec AlgebraicCurve.Divisor.degree_smul AlgebraicCurve.Pic0.mk_add AlgebraicCurve.Place.ord_zero AlgebraicCurve.Place.ofHeightOneSpectrum_toValuationSubring AlgebraicCurve.CurveModel.mk.injEq AlgebraicCurve.CurveModel.mk.sizeOf_spec compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁"
p2m_attr_erase "simp" "WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two"

set_option maxHeartbeats 8000000
open scoped WeierstrassCurve.Affine TensorProduct
open WeierstrassCurve WeierstrassCurve.Affine.Point

theorem solution
    (p : ℕ) [Fact p.Prime] (W : WeierstrassCurve ℤ_[p]) (hΔ : IsUnit W.Δ)
    [DecidableEq (AlgebraicClosure ℚ_[p])]
    (A : Type) [CommRing A] [HopfAlgebra ℚ_[p] A]
    (hAfin : Module.Finite ℚ_[p] A) (hAcocomm : Coalgebra.IsCocomm ℚ_[p] A)
    (eA : WithConv (A →ₐ[ℚ_[p]] AlgebraicClosure ℚ_[p]) ≃
          Submodule.torsionBy ℤ ((W⁄ℚ_[p])⁄(AlgebraicClosure ℚ_[p])).Point p)
    (heA_add : ∀ f g, eA (f * g) = eA f + eA g)
    (heA_act : ∀ (σ : AlgebraicClosure ℚ_[p] ≃ₐ[ℚ_[p]] AlgebraicClosure ℚ_[p])
      (f g : WithConv (A →ₐ[ℚ_[p]] AlgebraicClosure ℚ_[p])),
      (∀ a : A, g a = σ (f a)) → eA g = σ • (eA f)) :
    ∃ (H : Type) (_ : CommRing H) (_ : HopfAlgebra ℤ_[p] H),
      Module.Finite ℤ_[p] H ∧ Module.Free ℤ_[p] H ∧ Coalgebra.IsCocomm ℤ_[p] H ∧
      Module.finrank ℤ_[p] H = p ^ 2 ∧
      ∃ φ : (ℚ_[p] ⊗[ℤ_[p]] H) ≃ₐ[ℚ_[p]] A,
        ∀ x, Coalgebra.comul (R := ℚ_[p]) (φ x) =
          (TensorProduct.map φ.toLinearMap φ.toLinearMap) (Coalgebra.comul (R := ℚ_[p]) x) := by
  have BffH := WeierstrassCurve.exists_finiteFree_hopfAlgebra_padicInt_torsionBy_rank_psq_of_isUnit_discr p W hΔ
  have BffPhi :
      ∀ {M : Type} [AddCommGroup M]
        [DistribMulAction (AlgebraicClosure ℚ_[p] ≃ₐ[ℚ_[p]] AlgebraicClosure ℚ_[p]) M]
        (A' : Type) [CommRing A'] [HopfAlgebra ℚ_[p] A']
        (_ : Module.Finite ℚ_[p] A') (_ : Coalgebra.IsCocomm ℚ_[p] A')
        (eA' : WithConv (A' →ₐ[ℚ_[p]] AlgebraicClosure ℚ_[p]) ≃ M)
        (_ : ∀ f g, eA' (f * g) = eA' f + eA' g)
        (_ : ∀ (σ : AlgebraicClosure ℚ_[p] ≃ₐ[ℚ_[p]] AlgebraicClosure ℚ_[p])
          (f g : WithConv (A' →ₐ[ℚ_[p]] AlgebraicClosure ℚ_[p])),
          (∀ a : A', g a = σ (f a)) → eA' g = σ • (eA' f))
        (B' : Type) [CommRing B'] [HopfAlgebra ℚ_[p] B']
        (_ : Module.Finite ℚ_[p] B') (_ : Coalgebra.IsCocomm ℚ_[p] B')
        (eB' : WithConv (B' →ₐ[ℚ_[p]] AlgebraicClosure ℚ_[p]) ≃ M)
        (_ : ∀ f g, eB' (f * g) = eB' f + eB' g)
        (_ : ∀ (σ : AlgebraicClosure ℚ_[p] ≃ₐ[ℚ_[p]] AlgebraicClosure ℚ_[p])
          (f g : WithConv (B' →ₐ[ℚ_[p]] AlgebraicClosure ℚ_[p])),
          (∀ b : B', g b = σ (f b)) → eB' g = σ • (eB' f)),
      ∃ φ : B' ≃ₐ[ℚ_[p]] A',
        ∀ x, Coalgebra.comul (R := ℚ_[p]) (φ x) =
          (TensorProduct.map φ.toLinearMap φ.toLinearMap) (Coalgebra.comul (R := ℚ_[p]) x) :=
    @HopfAlgebra.exists_algEquiv_comul_of_withConv_equiv_algClosure_padic p _
  obtain ⟨H, _, _, hHfin, hHfree, hHcocomm, hrank, eH, heH_add, heH_act⟩ := BffH

  let ι := AlgHom.liftEquiv ℤ_[p] ℚ_[p] H (AlgebraicClosure ℚ_[p])
  let ιW : WithConv (ℚ_[p] ⊗[ℤ_[p]] H →ₐ[ℚ_[p]] AlgebraicClosure ℚ_[p]) ≃
           WithConv (H →ₐ[ℤ_[p]] AlgebraicClosure ℚ_[p]) :=
    ⟨fun g => WithConv.toConv (ι.symm g.ofConv), fun f => WithConv.toConv (ι f.ofConv),
     fun g => by simp only [WithConv.ofConv_toConv, Equiv.apply_symm_apply, WithConv.toConv_ofConv],
     fun f => by simp only [WithConv.ofConv_toConv, Equiv.symm_apply_apply, WithConv.toConv_ofConv]⟩
  have hιW_mul : ∀ F G, ιW (F * G) = ιW F * ιW G :=
    fun F G => AlgHom.liftEquiv_symm_withConv_mul ℤ_[p] ℚ_[p] H (AlgebraicClosure ℚ_[p]) F G
  let eB := ιW.trans eH
  have heB_add : ∀ f g, eB (f * g) = eB f + eB g := fun f g => by
    simp only [eB, Equiv.trans_apply, hιW_mul]; exact heH_add _ _
  have heB_act : ∀ (σ : AlgebraicClosure ℚ_[p] ≃ₐ[ℚ_[p]] AlgebraicClosure ℚ_[p])
      (f g : WithConv (ℚ_[p] ⊗[ℤ_[p]] H →ₐ[ℚ_[p]] AlgebraicClosure ℚ_[p])),
      (∀ b, g b = σ (f b)) → eB g = σ • (eB f) := fun σ f g hfg => by
    simp only [eB, Equiv.trans_apply]
    apply heH_act σ
    intro h

    show (ι.symm g.ofConv) h = σ ((ι.symm f.ofConv) h)
    rw [show ∀ (ψ : ℚ_[p] ⊗[ℤ_[p]] H →ₐ[ℚ_[p]] AlgebraicClosure ℚ_[p]) (h' : H),
          (ι.symm ψ) h' = ψ (1 ⊗ₜ[ℤ_[p]] h') from fun _ _ => rfl,
        show ∀ (ψ : ℚ_[p] ⊗[ℤ_[p]] H →ₐ[ℚ_[p]] AlgebraicClosure ℚ_[p]) (h' : H),
          (ι.symm ψ) h' = ψ (1 ⊗ₜ[ℤ_[p]] h') from fun _ _ => rfl]
    exact hfg (1 ⊗ₜ[ℤ_[p]] h)
  obtain ⟨φ, hφcomul⟩ :=
    BffPhi A hAfin hAcocomm eA heA_add heA_act (ℚ_[p] ⊗[ℤ_[p]] H)
      inferInstance inferInstance eB heB_add heB_act
  exact ⟨H, ‹_›, ‹_›, hHfin, hHfree, hHcocomm, hrank, φ, hφcomul⟩

end S_WeierstrassCurve_exists_finiteFree_hopfOrder_padicInt_rank_psq_of_isUnit_discr_of_hopfAlgebra_padic
end P2MW
export P2MW.S_WeierstrassCurve_exists_finiteFree_hopfOrder_padicInt_rank_psq_of_isUnit_discr_of_hopfAlgebra_padic (solution)
