-- Prove2me | solution 1 for WeierstrassProjModel.kw_lr_chartTensor_genericProj_pointClass_ne
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/176f08a6-cf8f-5471-8ddb-6817f75ec300

import Mathlib.AlgebraicGeometry.EllipticCurve.Projective.Point
import Mathlib.RingTheory.Localization.FractionRing
import Theorems.Thm_WeierstrassProjModel_isDomain_chartTensor_of_isElliptic
import Theorems.Thm_WeierstrassProjModel_chartEval_equation_and_apply_self_eq_one
import Theorems.Thm_WeierstrassProjModel_kw_lr_chartTensor_genProd_ne_genTensOne
import Definitions.Def_WeierstrassCurve_ProjModel_GroupLawVocabulary
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassProjModel_kw_lr_chartTensor_genericProj_pointClass_ne

set_option autoImplicit false
set_option maxHeartbeats 6400000
set_option synthInstance.maxHeartbeats 1600000

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

attribute [local instance] MvPolynomial.gradedAlgebra WeierstrassProjModel.kw_pbac_awayAlgebra in
theorem solution [IsDomain R] [IsNoetherianRing R] [W.IsElliptic] (i j : Fin 3) :
    haveI : IsDomain ((𝒜 i) ⊗[R] (𝒜 j)) := isDomain_chartTensor_of_isElliptic W i j
    let ψᵢ : (𝒜 i) →ₐ[R] FractionRing ((𝒜 i) ⊗[R] (𝒜 j)) :=
      (IsScalarTower.toAlgHom R ((𝒜 i) ⊗[R] (𝒜 j)) (FractionRing ((𝒜 i) ⊗[R] (𝒜 j)))).comp
        Algebra.TensorProduct.includeLeft
    let ψⱼ : (𝒜 j) →ₐ[R] FractionRing ((𝒜 i) ⊗[R] (𝒜 j)) :=
      (IsScalarTower.toAlgHom R ((𝒜 i) ⊗[R] (𝒜 j)) (FractionRing ((𝒜 i) ⊗[R] (𝒜 j)))).comp
        Algebra.TensorProduct.includeRight
    (⟦kw_lrApt_chartEval W (FractionRing ((𝒜 i) ⊗[R] (𝒜 j))) i ψᵢ⟧
        : WeierstrassCurve.Projective.PointClass (FractionRing ((𝒜 i) ⊗[R] (𝒜 j))))
      ≠ ⟦kw_lrApt_chartEval W (FractionRing ((𝒜 i) ⊗[R] (𝒜 j))) j ψⱼ⟧ := by
  haveI : IsDomain ((𝒜 i) ⊗[R] (𝒜 j)) := isDomain_chartTensor_of_isElliptic W i j
  intro ψᵢ ψⱼ heq
  obtain ⟨u, hu⟩ := Quotient.eq.mp heq
  let ι := algebraMap ((𝒜 i) ⊗[R] (𝒜 j)) (FractionRing ((𝒜 i) ⊗[R] (𝒜 j)))
  have hinj : Function.Injective ι :=
    IsFractionRing.injective ((𝒜 i) ⊗[R] (𝒜 j)) (FractionRing ((𝒜 i) ⊗[R] (𝒜 j)))
  have hevi : ∀ k, kw_lrApt_chartEval W _ i ψᵢ k
      = ι ((kw_lrChart_gen W i k) ⊗ₜ[R] (1 : (𝒜 j))) := fun k => rfl
  have hevj : ∀ k, kw_lrApt_chartEval W _ j ψⱼ k
      = ι ((1 : (𝒜 i)) ⊗ₜ[R] (kw_lrChart_gen W j k)) := fun k => rfl
  have hj1 : kw_lrApt_chartEval W _ j ψⱼ j = 1 :=
    (chartEval_equation_and_apply_self_eq_one W _ j ψⱼ).2

  have huj : (u : FractionRing ((𝒜 i) ⊗[R] (𝒜 j)))
      = ι ((kw_lrChart_gen W i j) ⊗ₜ[R] (1 : (𝒜 j))) := by
    have hc := congrFun hu j
    simp only [Pi.smul_apply, Units.smul_def, smul_eq_mul] at hc
    rw [hj1, mul_one] at hc
    exact hc.trans (hevi j)
  obtain ⟨k, hk⟩ := kw_lr_chartTensor_genProd_ne_genTensOne W i j
  apply hk
  apply hinj

  have huk : ι ((kw_lrChart_gen W i j) ⊗ₜ[R] (1 : (𝒜 j)))
      * ι ((1 : (𝒜 i)) ⊗ₜ[R] (kw_lrChart_gen W j k))
      = ι ((kw_lrChart_gen W i k) ⊗ₜ[R] (1 : (𝒜 j))) := by
    have hc := congrFun hu k
    simp only [Pi.smul_apply, Units.smul_def, smul_eq_mul] at hc
    rw [huj, hevj k] at hc
    exact hc.trans (hevi k)
  calc ι ((kw_lrChart_gen W i j) ⊗ₜ[R] (kw_lrChart_gen W j k))
      = ι ((kw_lrChart_gen W i j) ⊗ₜ[R] (1 : (𝒜 j)))
          * ι ((1 : (𝒜 i)) ⊗ₜ[R] (kw_lrChart_gen W j k)) := by
        rw [← map_mul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    _ = ι ((kw_lrChart_gen W i k) ⊗ₜ[R] (1 : (𝒜 j))) := huk

end

end S_WeierstrassProjModel_kw_lr_chartTensor_genericProj_pointClass_ne
end P2MW
export P2MW.S_WeierstrassProjModel_kw_lr_chartTensor_genericProj_pointClass_ne (solution)
