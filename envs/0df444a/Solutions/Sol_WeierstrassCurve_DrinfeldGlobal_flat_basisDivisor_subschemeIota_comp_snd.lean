-- Prove2me | solution 1 for WeierstrassCurve.DrinfeldGlobal.flat_basisDivisor_subschemeIota_comp_snd
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/bd4aaac6-83b2-5c0c-a6ca-e0e41d2e66f6

import Definitions.Def_WeierstrassCurve_ProjModel
import Definitions.Def_WeierstrassCurve_DrinfeldBasisGlobal
import Definitions.Def_WeierstrassCurve_DrinfeldTransportPin
import Theorems.Thm_AlgebraicGeometry_RelEffCartierDiv_exists_I_eq_prodKerGraph
import Theorems.Thm_WeierstrassProjModel_projModelStrCR_isProper
import Theorems.Thm_WeierstrassProjModel_projModelStrCR_smoothOfRelativeDimension_one
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_DrinfeldGlobal_flat_basisDivisor_subschemeIota_comp_snd
p2m_attr_erase "instance" "AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instNeg AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulInt AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instAddCommGroup AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instAdd AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSub AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instModuleCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulNat AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instZero WeierstrassProjModel.quotGradingSubmoduleDegreeZeroFiniteType WeierstrassProjModel.kw_lrChart_tensorCommRing WeierstrassProjModel.kw_lrChart_biGrading_gradedAlgebra WeierstrassProjModel.projModel_isIso_spec_mapCR WeierstrassProjModel.kw_lrSymOC_isDomain_ℬ₀ WeierstrassProjModel.isProper_projModelStrCR WeierstrassProjModel.homogeneousSubmoduleDegreeZeroFiniteType"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.sub_app AlgebraicGeometry.Scheme.IdealSheafData.sres_sresTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.add_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.mk.sizeOf_spec AlgebraicGeometry.Scheme.IdealSheafData.coe_resLE AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.smul_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.coe_ofLE_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.ideal_range AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.zero_app AlgebraicGeometry.Scheme.IdealSheafData.sres_sres AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.comp_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.neg_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.id_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.coe_mulRight_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.nsmul_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.mk.injEq AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.zsmul_app WeierstrassProjModel.kw_lrAdd_substHom_X WeierstrassProjModel.kw_lrSym_substHom_X"

set_option autoImplicit false

universe u

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits WeierstrassProjModel WeierstrassCurve.DrinfeldGlobal NeronModelInfra

theorem solution
    {T : Type u} [CommRing T] (W : WeierstrassCurve T) (hΔ : IsUnit W.Δ)
    (G : RelativeGroupLaw T (projModelStrCR W)) (n : ℕ) (P Q : Section W) :
    Flat ((basisDivisor G n P Q).subschemeι ≫ pullback.snd (projModelStrCR W) (𝟙 (Spec (CommRingCat.of T)))) := by
  haveI : WeierstrassCurve.IsElliptic W := ⟨hΔ⟩
  haveI : IsSeparated (projModelStrCR (W : WeierstrassCurve.Projective T)) :=
    (WeierstrassProjModel.projModelStrCR_isProper (W : WeierstrassCurve.Projective T)).toIsSeparated
  haveI : SmoothOfRelativeDimension 1 (projModelStrCR (W : WeierstrassCurve.Projective T)) :=
    WeierstrassProjModel.projModelStrCR_smoothOfRelativeDimension_one (W : WeierstrassCurve.Projective T)
  obtain ⟨D, hD⟩ := AlgebraicGeometry.RelEffCartierDiv.exists_I_eq_prodKerGraph
    (f := projModelStrCR W) (g := 𝟙 (Spec (CommRingCat.of T))) (basisTuple G n P Q) (basisTuple_over G n P Q)
  have h := D.flat
  rw [hD] at h
  exact h

end S_WeierstrassCurve_DrinfeldGlobal_flat_basisDivisor_subschemeIota_comp_snd
end P2MW
export P2MW.S_WeierstrassCurve_DrinfeldGlobal_flat_basisDivisor_subschemeIota_comp_snd (solution)
