-- Prove2me | solution 1 for WeierstrassProjModel.projMap_coefficientHom_comp_projMap_variableChangeHom_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/5c402b94-494c-5ff6-90ca-1808d487e9f0

import Mathlib
import Definitions.Def_WeierstrassCurve_ProjModel
import Definitions.Def_WeierstrassCurve_DrinfeldBasisGlobal
import Definitions.Def_WeierstrassCurve_DrinfeldTransportPin
import Definitions.Def_WeierstrassCurve_SectionAtOrigin
import Definitions.Def_WeierstrassCurve_ProjModel_GroupLawVocabulary
import Definitions.Def_WeierstrassCurve_DrinfeldLevelFunctor
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassProjModel_projMap_coefficientHom_comp_projMap_variableChangeHom_eq

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory NeronModelInfra WeierstrassProjModel WeierstrassCurve.DrinfeldGlobal

attribute [local instance] MvPolynomial.gradedAlgebra

theorem solution
    (T T' : Type) [CommRing T] [CommRing T'] (f : T →+* T')
    (W : WeierstrassCurve T) (C : WeierstrassCurve.VariableChange T)
    (hmap : (C • W).map f = C.map f • W.map f)
    (φ : projModelGradingCR W.toProjective →+*ᵍ projModelGradingCR (C • W).toProjective)
    (hφ : HomogeneousIdeal.irrelevant (projModelGradingCR (C • W).toProjective) ≤
      (HomogeneousIdeal.irrelevant (projModelGradingCR W.toProjective)).map φ)
    (hφC : IsVariableChangeHom W.toProjective C φ)
    (φ' : projModelGradingCR (W.map f).toProjective →+*ᵍ projModelGradingCR (C.map f • W.map f).toProjective)
    (hφ' : HomogeneousIdeal.irrelevant (projModelGradingCR (C.map f • W.map f).toProjective) ≤
      (HomogeneousIdeal.irrelevant (projModelGradingCR (W.map f).toProjective)).map φ')
    (hφ'C : IsVariableChangeHom (W.map f).toProjective (C.map f) φ')
    (γ : projModelGradingCR W.toProjective →+*ᵍ projModelGradingCR (W.map f).toProjective)
    (hγ : HomogeneousIdeal.irrelevant (projModelGradingCR (W.map f).toProjective) ≤
      (HomogeneousIdeal.irrelevant (projModelGradingCR W.toProjective)).map γ)
    (hγf : IsCoefficientHom W.toProjective f γ)
    (γC : projModelGradingCR (C • W).toProjective →+*ᵍ projModelGradingCR ((C • W).map f).toProjective)
    (hγC : HomogeneousIdeal.irrelevant (projModelGradingCR ((C • W).map f).toProjective) ≤
      (HomogeneousIdeal.irrelevant (projModelGradingCR (C • W).toProjective)).map γC)
    (hγCf : IsCoefficientHom (C • W).toProjective f γC) :
    Proj.map γC hγC ≫ Proj.map φ hφ =
      eqToHom (congrArg projModelCR (congrArg WeierstrassCurve.toProjective hmap)) ≫ Proj.map φ' hφ' ≫ Proj.map γ hγ := by

  obtain ⟨hγCa0, hγCX0⟩ := hγCf
  have hγCa : ∀ a : T, γC (cls (C • W).toProjective (MvPolynomial.C a)) =
      cls ((C • W).map f).toProjective (MvPolynomial.C (f a)) := hγCa0
  have hγCX : ∀ i : Fin 3, γC (cls (C • W).toProjective (MvPolynomial.X i)) =
      cls ((C • W).map f).toProjective (MvPolynomial.X i) := hγCX0
  clear hγCa0 hγCX0
  revert γC hγC hγCa hγCX hmap
  generalize (C • W).map f = V
  intro hmap γC hγC hγCa hγCX
  subst hmap
  rw [eqToHom_refl, Category.id_comp]

  obtain ⟨hφa, hφ0, hφ1, hφ2⟩ := hφC
  obtain ⟨hφ'a, hφ'0, hφ'1, hφ'2⟩ := hφ'C
  obtain ⟨hγa, hγX⟩ := hγf
  simp only [cls] at hφa hφ0 hφ1 hφ2 hφ'a hφ'0 hφ'1 hφ'2 hγa hγX hγCa hγCX
  have key : γC.comp φ = φ'.comp γ := by
    apply GradedRingHom.ext
    intro x
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
    set F := (γC.comp φ).toRingHom.comp (Ideal.Quotient.mk (projModelHomogeneousIdealCR W.toProjective).toIdeal)
      with hFdef
    set G := (φ'.comp γ).toRingHom.comp (Ideal.Quotient.mk (projModelHomogeneousIdealCR W.toProjective).toIdeal)
      with hGdef
    have hF : F = G := by
      apply MvPolynomial.ringHom_ext
      · intro a
        simp only [hFdef, hGdef, RingHom.comp_apply, GradedRingHom.coe_toRingHom, GradedRingHom.comp_apply,
          hφa, hγCa, hγa, hφ'a]
      · intro i
        fin_cases i
        · change F (MvPolynomial.X 0) = G (MvPolynomial.X 0)
          simp only [hFdef, hGdef, RingHom.comp_apply, GradedRingHom.coe_toRingHom, GradedRingHom.comp_apply,
            hφ0, hγX, hφ'0]
          simp only [map_add, map_mul, map_pow, hγCX, hγCa, WeierstrassCurve.VariableChange.map_u,
            WeierstrassCurve.VariableChange.map_r, Units.coe_map, MonoidHom.coe_coe]
        · change F (MvPolynomial.X 1) = G (MvPolynomial.X 1)
          simp only [hFdef, hGdef, RingHom.comp_apply, GradedRingHom.coe_toRingHom, GradedRingHom.comp_apply,
            hφ1, hγX, hφ'1]
          simp only [map_add, map_mul, map_pow, hγCX, hγCa, WeierstrassCurve.VariableChange.map_u,
            WeierstrassCurve.VariableChange.map_s, WeierstrassCurve.VariableChange.map_t, Units.coe_map,
            MonoidHom.coe_coe]
        · change F (MvPolynomial.X 2) = G (MvPolynomial.X 2)
          simp only [hFdef, hGdef, RingHom.comp_apply, GradedRingHom.coe_toRingHom, GradedRingHom.comp_apply,
            hφ2, hγX, hφ'2, hγCX]
    exact RingHom.congr_fun hF p
  have gen : ∀ (ψ₁ ψ₂ : projModelGradingCR W.toProjective →+*ᵍ projModelGradingCR (C.map f • W.map f).toProjective)
      (h₁ : HomogeneousIdeal.irrelevant (projModelGradingCR (C.map f • W.map f).toProjective) ≤
        (HomogeneousIdeal.irrelevant (projModelGradingCR W.toProjective)).map ψ₁)
      (h₂ : HomogeneousIdeal.irrelevant (projModelGradingCR (C.map f • W.map f).toProjective) ≤
        (HomogeneousIdeal.irrelevant (projModelGradingCR W.toProjective)).map ψ₂),
      ψ₁ = ψ₂ → Proj.map ψ₁ h₁ = Proj.map ψ₂ h₂ := by
    rintro _ _ _ _ rfl; rfl
  rw [← Proj.map_comp, ← Proj.map_comp]
  exact gen _ _ _ _ key

end S_WeierstrassProjModel_projMap_coefficientHom_comp_projMap_variableChangeHom_eq
end P2MW
export P2MW.S_WeierstrassProjModel_projMap_coefficientHom_comp_projMap_variableChangeHom_eq (solution)
