-- Prove2me | solution 1 for WeierstrassCurve.DrinfeldGlobal.exists_variableChange_map_fstHom_eq_one_and_smul_eq_of_iso_of_projMap_comp_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/e82d5657-33e0-5866-8604-ea23bbd8b424

import Definitions.Def_WeierstrassCurve_ProjModel
import Definitions.Def_WeierstrassCurve_DrinfeldBasisGlobal
import Definitions.Def_WeierstrassCurve_DrinfeldTransportPin
import Definitions.Def_WeierstrassCurve_SectionAtOrigin
import Definitions.Def_WeierstrassCurve_ProjModel_GroupLawVocabulary
import Theorems.Thm_WeierstrassProjModel_exists_variableChange_smul_eq_and_projMap_eq_inv_of_iso_of_kwZeroSect_comp_eq_of_isArtinianRing
import Theorems.Thm_WeierstrassProjModel_variableChange_eq_one_of_projMap_eq_id
import Theorems.Thm_WeierstrassProjModel_projMap_coefficientHom_comp_projMap_variableChangeHom_eq
import Theorems.Thm_WeierstrassProjModel_exists_isVariableChangeHom_isIso_projMap
import Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_isPullback_projMap_of_isCoefficientHom
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_DrinfeldGlobal_exists_variableChange_map_fstHom_eq_one_and_smul_eq_of_iso_of_projMap_comp_eq
p2m_attr_erase "simp" "WeierstrassCurve.wIter_zero MvPowerSeries.kw_coeff_pderiv FormalGroup.nthSeries_zero FormalGroup.evalNSMul_zero"

set_option autoImplicit false
open AlgebraicGeometry CategoryTheory NeronModelInfra WeierstrassProjModel WeierstrassCurve.DrinfeldGlobal
attribute [local instance] MvPolynomial.gradedAlgebra

theorem solution
    (k : Type) [Field k]
    (W W' : WeierstrassCurve (DualNumber k)) (hΔ : IsUnit W.Δ)
    (hW' : W'.map (TrivSqZeroExt.fstHom k k k).toRingHom = W.map (TrivSqZeroExt.fstHom k k k).toRingHom)
    (Ψ : projModelCR W.toProjective ≅ projModelCR W'.toProjective)
    (hΨ : Ψ.hom ≫ projModelStrCR W'.toProjective = projModelStrCR W.toProjective)
    (hΨO : (kwZeroSect (DualNumber k) W).1 ≫ Ψ.hom = (kwZeroSect (DualNumber k) W').1)
    (hΨred : ∃ (φ : projModelGradingCR W.toProjective →+*ᵍ
          projModelGradingCR (W.map (TrivSqZeroExt.fstHom k k k).toRingHom).toProjective)
        (hφ : HomogeneousIdeal.irrelevant (projModelGradingCR (W.map (TrivSqZeroExt.fstHom k k k).toRingHom).toProjective) ≤
          (HomogeneousIdeal.irrelevant (projModelGradingCR W.toProjective)).map φ)
        (φ' : projModelGradingCR W'.toProjective →+*ᵍ
          projModelGradingCR (W'.map (TrivSqZeroExt.fstHom k k k).toRingHom).toProjective)
        (hφ' : HomogeneousIdeal.irrelevant (projModelGradingCR (W'.map (TrivSqZeroExt.fstHom k k k).toRingHom).toProjective) ≤
          (HomogeneousIdeal.irrelevant (projModelGradingCR W'.toProjective)).map φ'),
        IsCoefficientHom W.toProjective (TrivSqZeroExt.fstHom k k k).toRingHom φ ∧
        IsCoefficientHom W'.toProjective (TrivSqZeroExt.fstHom k k k).toRingHom φ' ∧
        Proj.map φ hφ ≫ Ψ.hom =
          eqToHom (congrArg projModelCR (congrArg WeierstrassCurve.toProjective hW')).symm ≫
            Proj.map φ' hφ') :
    ∃ C : WeierstrassCurve.VariableChange (DualNumber k),
      C.map (TrivSqZeroExt.fstHom k k k).toRingHom = 1 ∧ C • W = W' := by
  classical

  haveI : IsArtinianRing (DualNumber k) := by
    haveI : Module.Finite k (DualNumber k) :=
      Module.Finite.equiv (R := k) (M := k × k)
        { toFun := id, invFun := id, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl,
          left_inv := fun _ => rfl, right_inv := fun _ => rfl }
    exact IsArtinianRing.of_finite k (DualNumber k)
  set π : DualNumber k →+* k := (TrivSqZeroExt.fstHom k k k).toRingHom with hπ
  have hπsurj : Function.Surjective π := fun a => ⟨TrivSqZeroExt.inl a, by rw [hπ]; rfl⟩

  have hΔ' : IsUnit W'.Δ := by
    rw [TrivSqZeroExt.isUnit_iff_isUnit_fst]
    have h1 : (W'.map π).Δ = (W.map π).Δ := by rw [hW']
    rw [WeierstrassCurve.map_Δ, WeierstrassCurve.map_Δ] at h1
    have h2 : IsUnit (π W.Δ) := hΔ.map π
    rw [← h1] at h2
    exact h2

  obtain ⟨C, hC, φ, hφ, hφC, hinv⟩ :=
    WeierstrassProjModel.exists_variableChange_smul_eq_and_projMap_eq_inv_of_iso_of_kwZeroSect_comp_eq_of_isArtinianRing
      (DualNumber k) W W' hΔ hΔ' Ψ hΨ hΨO
  refine ⟨C, ?_, hC⟩

  obtain ⟨γ, hγ, γ', hγ', hγcoef, hγ'coef, hsq⟩ := hΨred
  subst hC
  have hmap : (C • W).map π = C.map π • W.map π := (W.map_variableChange C π).symm
  have hC₀ : C.map π • W.map π = W.map π := hmap.symm.trans hW'
  have hΔ₀ : IsUnit (W.map π).Δ := by rw [WeierstrassCurve.map_Δ]; exact hΔ.map π

  obtain ⟨φ₀, hφ₀, hφ₀C, -, -⟩ :=
    WeierstrassProjModel.exists_isVariableChangeHom_isIso_projMap (W.map π).toProjective (C.map π)

  have hnat := WeierstrassProjModel.projMap_coefficientHom_comp_projMap_variableChangeHom_eq
    (DualNumber k) k π W C hmap φ hφ hφC φ₀ hφ₀ hφ₀C γ hγ hγcoef γ' hγ' hγ'coef

  haveI : IsClosedImmersion (Spec.map (CommRingCat.ofHom π)) := IsClosedImmersion.spec_of_surjective _ hπsurj
  haveI : IsClosedImmersion (Proj.map γ hγ) :=
    MorphismProperty.of_isPullback (P := @IsClosedImmersion)
      (WeierstrassCurve.DrinfeldGlobal.isPullback_projMap_of_isCoefficientHom W.toProjective π γ hγ hγcoef).flip
      inferInstance

  have key : (eqToHom (congrArg projModelCR (congrArg WeierstrassCurve.toProjective hC₀)).symm ≫ Proj.map φ₀ hφ₀) ≫
      Proj.map γ hγ = 𝟙 _ ≫ Proj.map γ hγ := by
    have h1 : Proj.map γ hγ ≫ Ψ.hom ≫ Ψ.inv = Proj.map γ hγ := by rw [Ψ.hom_inv_id, Category.comp_id]
    rw [← Category.assoc, hsq, ← hinv, Category.assoc, eqToHom_refl, Category.id_comp, hnat] at h1
    rw [Category.id_comp]

    simpa only [Category.assoc, eqToHom_trans_assoc, eqToHom_trans] using h1
  have hid : eqToHom (congrArg projModelCR (congrArg WeierstrassCurve.toProjective hC₀)).symm ≫ Proj.map φ₀ hφ₀ = 𝟙 _ := by
    rw [← cancel_mono (Proj.map γ hγ)]
    exact key
  exact WeierstrassProjModel.variableChange_eq_one_of_projMap_eq_id k (W.map π) hΔ₀ (C.map π) hC₀ φ₀ hφ₀ hφ₀C hid

end S_WeierstrassCurve_DrinfeldGlobal_exists_variableChange_map_fstHom_eq_one_and_smul_eq_of_iso_of_projMap_comp_eq
end P2MW
export P2MW.S_WeierstrassCurve_DrinfeldGlobal_exists_variableChange_map_fstHom_eq_one_and_smul_eq_of_iso_of_projMap_comp_eq (solution)
