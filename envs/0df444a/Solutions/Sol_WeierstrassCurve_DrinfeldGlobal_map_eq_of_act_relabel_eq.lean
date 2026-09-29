-- Prove2me | solution 1 for WeierstrassCurve.DrinfeldGlobal.map_eq_of_act_relabel_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/ee6993dd-f68a-5067-9632-b721bcea1276

import Mathlib
import Definitions.Def_ModularCurve_KatzLevelP
import Definitions.Def_ModularCurve_LevelRelabelling
import Definitions.Def_WeierstrassCurve_ProjModel
import Definitions.Def_WeierstrassCurve_DrinfeldBasisGlobal
import Definitions.Def_WeierstrassCurve_DrinfeldTransportPin
import Definitions.Def_WeierstrassCurve_SectionAtOrigin
import Definitions.Def_WeierstrassCurve_DrinfeldLevelFunctor
import Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_LevelTransport_exists_act_neg_comp_eqToHom_eq_inv
import Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_IsDrinfeldBasis_map_eq_smul_one_of_zlinComb_eq_zsmulSection
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_DrinfeldGlobal_map_eq_of_act_relabel_eq
p2m_attr_erase "instance" "WeierstrassProjModel.quotGradingSubmoduleDegreeZeroFiniteType WeierstrassProjModel.kw_lrChart_tensorCommRing WeierstrassProjModel.kw_lrChart_biGrading_gradedAlgebra WeierstrassProjModel.projModel_isIso_spec_mapCR WeierstrassProjModel.kw_lrSymOC_isDomain_ℬ₀ WeierstrassProjModel.isProper_projModelStrCR WeierstrassProjModel.homogeneousSubmoduleDegreeZeroFiniteType instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly"
p2m_attr_erase "simp" "WeierstrassProjModel.kw_lrAdd_substHom_X WeierstrassProjModel.kw_lrSym_substHom_X WeierstrassProjModel.kw_lrThird_substHom_X compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two"

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry NeronModelInfra WeierstrassProjModel WeierstrassCurve.DrinfeldGlobal ModularCurve

namespace DrinfeldSignAssembly

theorem fst_comp_eqToHom_eq {K : Type} [CommRing K] {z : RawDrinfeldPair K}
    {c : WeierstrassCurve.Projective K} {P Q : Section c}
    (h : z = ⟨c, P, Q⟩) (hc : z.curve = c) :
    z.P.1 ≫ eqToHom (congrArg projModelCR hc) = P.1 ∧ z.Q.1 ≫ eqToHom (congrArg projModelCR hc) = Q.1 := by
  subst h
  constructor <;> simp

end DrinfeldSignAssembly

open DrinfeldSignAssembly in

theorem solution
    {A : Type} [CommRing A] (𝒢 : GroupLaws A) (h𝒢 : 𝒢.IsChordTangent) (h𝒢O : 𝒢.IsOriginIdentity)
    (q : ℕ) [Fact q.Prime] (𝒯 : LevelTransport A 𝒢 q) (h𝒯 : 𝒯.IsSectionTransport)
    (hVC : ∀ (T : Type) [CommRing T] [Algebra A T] (W : WeierstrassCurve.Projective T) (C : WeierstrassCurve.VariableChange T),
      ∃ (φ : projModelGradingCR W →+*ᵍ projModelGradingCR (C • W))
        (_ : HomogeneousIdeal.irrelevant (projModelGradingCR (C • W)) ≤ (HomogeneousIdeal.irrelevant (projModelGradingCR W)).map φ),
        IsVariableChangeHom W C φ)
    (K : Type) [Field K] [Algebra A K] (hqK : (q : K) ≠ 0)
    (W : WeierstrassCurve.Projective K) (x : RawDrinfeldPair K) (hΔ : IsUnit x.curve.Δ)
    (hx : RawDrinfeldPair.IsLevel 𝒢 q W x)
    (g : Matrix (Fin 2) (Fin 2) ℤ) (C : WeierstrassCurve.VariableChange K)
    (h : 𝒯.act C (ModularCurve.LevelRelabelling.RawDrinfeldPair.relabel 𝒢 g x hΔ) = x) :
    (C = 1 → g.map (Int.castRingHom (ZMod q)) = 1) ∧
      (C = ⟨-1, 0, -x.curve.a₁, -x.curve.a₃⟩ → g.map (Int.castRingHom (ZMod q)) = -1) := by
  classical
  obtain ⟨c, P, Q⟩ := x
  obtain ⟨hcW, hΔ0, hbasis⟩ := hx

  obtain ⟨ev, hev⟩ := h𝒢 K c hΔ
  set G := 𝒢 K c hΔ with hG
  have hbasis' : IsDrinfeldBasis G q P Q := hbasis
  have h1 : ModularCurve.LevelRelabelling.zsmulSection G 1 P = P := G.nsmul_one_apply _ P
  have h1Q : ModularCurve.LevelRelabelling.zsmulSection G 1 Q = Q := G.nsmul_one_apply _ Q
  have hm1 : ∀ R : Section c, ModularCurve.LevelRelabelling.zsmulSection G (-1) R = G.inv _ R := fun R => by
    show G.inv _ (G.nsmul _ (0 + 1) R) = G.inv _ R
    rw [G.nsmul_one_apply]
  refine ⟨fun hC => ?_, fun hC => ?_⟩
  ·
    subst hC
    rw [𝒯.act_one] at h

    have h' := h
    simp only [ModularCurve.LevelRelabelling.RawDrinfeldPair.relabel, RawDrinfeldPair.mk.injEq, heq_eq_eq,
      true_and] at h'
    obtain ⟨hP, hQ⟩ := h'
    have := WeierstrassCurve.DrinfeldGlobal.IsDrinfeldBasis.map_eq_smul_one_of_zlinComb_eq_zsmulSection
      c hΔ G ev hev q hqK P Q hbasis' g 1 (Or.inl rfl) (hP.trans h1.symm) (hQ.trans h1Q.symm)
    simpa using this
  ·
    subst hC
    obtain ⟨hc, hPneg, hQneg⟩ :=
      WeierstrassCurve.DrinfeldGlobal.LevelTransport.exists_act_neg_comp_eqToHom_eq_inv 𝒢 h𝒢 h𝒢O q 𝒯 h𝒯 hVC K
        (ModularCurve.LevelRelabelling.RawDrinfeldPair.relabel 𝒢 g ⟨c, P, Q⟩ hΔ) hΔ

    have hc2 : (𝒯.act ⟨-1, 0, -(RawDrinfeldPair.mk c P Q).curve.a₁, -(RawDrinfeldPair.mk c P Q).curve.a₃⟩
        (ModularCurve.LevelRelabelling.RawDrinfeldPair.relabel 𝒢 g ⟨c, P, Q⟩ hΔ)).curve = c :=
      (congrArg RawDrinfeldPair.curve h).trans rfl
    obtain ⟨hP2, hQ2⟩ := fst_comp_eqToHom_eq h hc2
    have hPeq : P.1 = (G.inv _ (ModularCurve.LevelRelabelling.zlinComb G P Q (g 0 0) (g 1 0))).1 :=
      hP2.symm.trans hPneg
    have hQeq : Q.1 = (G.inv _ (ModularCurve.LevelRelabelling.zlinComb G P Q (g 0 1) (g 1 1))).1 :=
      hQ2.symm.trans hQneg
    letI grp := G.pointGroup (𝟙 (WeierstrassCurve.DrinfeldGlobal.base (T := K)))
    have eP : ModularCurve.LevelRelabelling.zlinComb G P Q (g 0 0) (g 1 0) = G.inv _ P := by
      have hP' : P = G.inv _ (ModularCurve.LevelRelabelling.zlinComb G P Q (g 0 0) (g 1 0)) := Subtype.ext hPeq
      conv_rhs => rw [hP']
      exact (inv_inv _).symm
    have eQ : ModularCurve.LevelRelabelling.zlinComb G P Q (g 0 1) (g 1 1) = G.inv _ Q := by
      have hQ' : Q = G.inv _ (ModularCurve.LevelRelabelling.zlinComb G P Q (g 0 1) (g 1 1)) := Subtype.ext hQeq
      conv_rhs => rw [hQ']
      exact (inv_inv _).symm
    have := WeierstrassCurve.DrinfeldGlobal.IsDrinfeldBasis.map_eq_smul_one_of_zlinComb_eq_zsmulSection
      c hΔ G ev hev q hqK P Q hbasis' g (-1) (Or.inr rfl) (eP.trans (hm1 P).symm) (eQ.trans (hm1 Q).symm)
    simpa using this

end S_WeierstrassCurve_DrinfeldGlobal_map_eq_of_act_relabel_eq
end P2MW
export P2MW.S_WeierstrassCurve_DrinfeldGlobal_map_eq_of_act_relabel_eq (solution)
