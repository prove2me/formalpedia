-- Prove2me | solution 1 for WeierstrassProjModel.kw_ev_genericPoint_zChart_addMap_self_ne_zeroClass
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/85d93f94-4fbb-5112-a1f2-958d7ce4fe5b

import Mathlib.AlgebraicGeometry.EllipticCurve.Projective.Point
import Definitions.Def_WeierstrassCurve_ProjModel
import Definitions.Def_WeierstrassCurve_ProjModel_GroupLawVocabulary
import Theorems.Thm_WeierstrassProjModel_exists_pointEval
import Theorems.Thm_WeierstrassProjModel_projModelStrCR_smoothOfRelativeDimension_one
import Theorems.Thm_WeierstrassProjModel_kw_hgi_geometricallyIntegral_of_baseChangeIso
import Theorems.Thm_WeierstrassProjModel_projModel_pullback_iso_baseChange
import Theorems.Thm_WeierstrassProjModel_chartEval_equation_and_apply_self_eq_one
import Theorems.Thm_WeierstrassProjModel_kw_ev_genericPoint_zChart_psi_injective
import Theorems.Thm_WeierstrassProjModel_kw_lrChart_negY_gen_ne_zero
import Mathlib.AlgebraicGeometry.FunctionField
import Mathlib.AlgebraicGeometry.Geometrically.Integral
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassProjModel_kw_ev_genericPoint_zChart_addMap_self_ne_zeroClass

set_option autoImplicit false
set_option maxHeartbeats 6400000
set_option synthInstance.maxHeartbeats 1600000
set_option Elab.async false
set_option linter.unusedSimpArgs false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra WeierstrassProjModel
open MvPolynomial WeierstrassCurve HomogeneousLocalization
open scoped TensorProduct

universe u

attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local instance] WeierstrassProjModel.kw_pbac_awayAlgebra

variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

set_option quotPrecheck false in
local notation "𝒜" i => HomogeneousLocalization.Away (projModelGradingCR W.toProjective)
  (Ideal.Quotient.mk (projModelHomogeneousIdealCR W.toProjective).toIdeal
    (X i : MvPolynomial (Fin 3) R))

theorem solution [IsDomain R] [IsNoetherianRing R] [W.IsElliptic] :
    haveI : Smooth (projModelStrCR W.toProjective) :=
      (projModelStrCR_smoothOfRelativeDimension_one W.toProjective).smooth
    haveI : GeometricallyIntegral (projModelStrCR W.toProjective) :=
      kw_hgi_geometricallyIntegral_of_baseChangeIso W
        (projModel_pullback_iso_baseChange W.toProjective)
    haveI : IsIntegral (projModelCR W.toProjective) :=
      GeometricallyIntegral.isIntegral_of_isLocallyNoetherian (projModelStrCR W.toProjective)
    letI : Algebra R (projModelCR W.toProjective).functionField :=
      (Spec.preimage ((projModelCR W.toProjective).fromSpecStalk
        (genericPoint (projModelCR W.toProjective)) ≫ projModelStrCR W.toProjective)).hom.toAlgebra
    have hΔF : algebraMap R (projModelCR W.toProjective).functionField W.Δ ≠ 0 :=
      (W.isUnit_Δ.map _).ne_zero
    ∀ (ψ : HomogeneousLocalization.Away (projModelGradingCR W.toProjective)
          (Ideal.Quotient.mk (projModelHomogeneousIdealCR W.toProjective).toIdeal
            (MvPolynomial.X (2 : Fin 3) : MvPolynomial (Fin 3) R)) →ₐ[R] (projModelCR W.toProjective).functionField),
      (projModelCR W.toProjective).fromSpecStalk (genericPoint (projModelCR W.toProjective))
        = Spec.map (CommRingCat.ofHom ψ.toRingHom)
            ≫ (projModelAffineOpenCoverCR R W.toProjective).openCover.f (2 : Fin 3)
      → (kw_lrApt_WF W (projModelCR W.toProjective).functionField).addMap
          ⟦kw_lrApt_chartEval W (projModelCR W.toProjective).functionField (2 : Fin 3) ψ⟧
          ⟦kw_lrApt_chartEval W (projModelCR W.toProjective).functionField (2 : Fin 3) ψ⟧
        ≠ ⟦![(0 : (projModelCR W.toProjective).functionField), 1, 0]⟧ := by

  haveI : Smooth (projModelStrCR W.toProjective) :=
    (projModelStrCR_smoothOfRelativeDimension_one W.toProjective).smooth
  haveI : GeometricallyIntegral (projModelStrCR W.toProjective) :=
    kw_hgi_geometricallyIntegral_of_baseChangeIso W
      (projModel_pullback_iso_baseChange W.toProjective)
  haveI : IsLocallyNoetherian (projModelCR W.toProjective) :=
    LocallyOfFiniteType.isLocallyNoetherian (projModelStrCR W.toProjective)
  haveI : IsIntegral (projModelCR W.toProjective) :=
    GeometricallyIntegral.isIntegral_of_isLocallyNoetherian (projModelStrCR W.toProjective)
  letI : Algebra R (projModelCR W.toProjective).functionField :=
    (Spec.preimage ((projModelCR W.toProjective).fromSpecStalk
      (genericPoint (projModelCR W.toProjective)) ≫ projModelStrCR W.toProjective)).hom.toAlgebra
  intro hΔF ψ hfac hcontra

  obtain ⟨hEq, hP2⟩ := chartEval_equation_and_apply_self_eq_one W (projModelCR W.toProjective).functionField (2 : Fin 3) ψ
  have hPz : kw_lrApt_chartEval W (projModelCR W.toProjective).functionField (2 : Fin 3) ψ 2 ≠ 0 := hP2 ▸ one_ne_zero
  classical

  have hYeq : kw_lrApt_chartEval W (projModelCR W.toProjective).functionField (2 : Fin 3) ψ 1 = (kw_lrApt_WF W (projModelCR W.toProjective).functionField).negY (kw_lrApt_chartEval W (projModelCR W.toProjective).functionField (2 : Fin 3) ψ) := by
    by_contra hYne
    have hxy : ¬((kw_lrApt_chartEval W (projModelCR W.toProjective).functionField (2 : Fin 3) ψ 0) * (kw_lrApt_chartEval W (projModelCR W.toProjective).functionField (2 : Fin 3) ψ 2) = (kw_lrApt_chartEval W (projModelCR W.toProjective).functionField (2 : Fin 3) ψ 0) * (kw_lrApt_chartEval W (projModelCR W.toProjective).functionField (2 : Fin 3) ψ 2)
        ∧ (kw_lrApt_chartEval W (projModelCR W.toProjective).functionField (2 : Fin 3) ψ 1) * (kw_lrApt_chartEval W (projModelCR W.toProjective).functionField (2 : Fin 3) ψ 2) = (kw_lrApt_WF W (projModelCR W.toProjective).functionField).negY (kw_lrApt_chartEval W (projModelCR W.toProjective).functionField (2 : Fin 3) ψ) * (kw_lrApt_chartEval W (projModelCR W.toProjective).functionField (2 : Fin 3) ψ 2)) := by
      rintro ⟨-, hy'⟩; exact hYne (mul_right_cancel₀ hPz hy')
    have hadd := WeierstrassCurve.Projective.addMap_of_Z_ne_zero
      (W := (kw_lrApt_WF W (projModelCR W.toProjective).functionField)) hEq hEq hPz hPz hxy
    rw [hcontra] at hadd
    obtain ⟨u, hu⟩ := Quotient.eq.mp hadd
    have hu2 := congrFun hu 2
    simp only [Pi.smul_apply, Units.smul_def, smul_eq_mul, Matrix.cons_val_two,
      Matrix.tail_cons, Matrix.head_cons, mul_one] at hu2
    exact u.ne_zero hu2

  have hnY : (kw_lrApt_WF W (projModelCR W.toProjective).functionField).negY (kw_lrApt_chartEval W (projModelCR W.toProjective).functionField (2 : Fin 3) ψ)
      = -(kw_lrApt_chartEval W (projModelCR W.toProjective).functionField (2 : Fin 3) ψ 1) - (kw_lrApt_WF W (projModelCR W.toProjective).functionField).a₁ * (kw_lrApt_chartEval W (projModelCR W.toProjective).functionField (2 : Fin 3) ψ 0) - (kw_lrApt_WF W (projModelCR W.toProjective).functionField).a₃ * (kw_lrApt_chartEval W (projModelCR W.toProjective).functionField (2 : Fin 3) ψ 2) := rfl
  have h0 : (2 : (projModelCR W.toProjective).functionField) * (kw_lrApt_chartEval W (projModelCR W.toProjective).functionField (2 : Fin 3) ψ 1) + (kw_lrApt_WF W (projModelCR W.toProjective).functionField).a₁ * (kw_lrApt_chartEval W (projModelCR W.toProjective).functionField (2 : Fin 3) ψ 0) + (kw_lrApt_WF W (projModelCR W.toProjective).functionField).a₃ = 0 := by
    linear_combination hYeq + hnY - (kw_lrApt_WF W (projModelCR W.toProjective).functionField).a₃ * hP2

  have ha₁ : (kw_lrApt_WF W (projModelCR W.toProjective).functionField).a₁ = algebraMap R (projModelCR W.toProjective).functionField W.a₁ := rfl
  have ha₃ : (kw_lrApt_WF W (projModelCR W.toProjective).functionField).a₃ = algebraMap R (projModelCR W.toProjective).functionField W.a₃ := rfl
  have hP0 : kw_lrApt_chartEval W (projModelCR W.toProjective).functionField (2 : Fin 3) ψ 0 = ψ (kw_lrChart_gen W 2 0) := rfl
  have hP1 : kw_lrApt_chartEval W (projModelCR W.toProjective).functionField (2 : Fin 3) ψ 1 = ψ (kw_lrChart_gen W 2 1) := rfl
  have helt : ψ ((2 : (𝒜 (2:Fin 3))) * kw_lrChart_gen W 2 1
      + (algebraMap R (𝒜 (2:Fin 3)) W.a₁) * kw_lrChart_gen W 2 0
      + algebraMap R (𝒜 (2:Fin 3)) W.a₃) = 0 := by
    rw [map_add, map_add, map_mul, map_mul, map_ofNat, AlgHom.commutes, AlgHom.commutes,
      ← hP0, ← hP1, ← ha₁, ← ha₃]
    exact h0

  exact kw_lrChart_negY_gen_ne_zero W
    ((kw_ev_genericPoint_zChart_psi_injective W ψ hfac) (helt.trans (map_zero ψ).symm))

end

end S_WeierstrassProjModel_kw_ev_genericPoint_zChart_addMap_self_ne_zeroClass
end P2MW
export P2MW.S_WeierstrassProjModel_kw_ev_genericPoint_zChart_addMap_self_ne_zeroClass (solution)
