-- Prove2me | solution 1 for WeierstrassProjModel.exists_lrSixU_ne_zero_xzcharts
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/89c591de-6d1a-5179-bb7d-2ead76db54d8

import Definitions.Def_WeierstrassCurve_ProjModel_GroupLawVocabulary
import Theorems.Thm_WeierstrassProjModel_isDomain_chartTensor_of_isElliptic
import Theorems.Thm_WeierstrassProjModel_kw_a2_exists_sixU_ne_zero_of_pointClass_ne
import Theorems.Thm_WeierstrassProjModel_kw_lr_chartTensor_genericProj_pointClass_ne
import Mathlib.AlgebraicGeometry.EllipticCurve.Projective.Point
import Mathlib.RingTheory.Localization.FractionRing
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassProjModel_exists_lrSixU_ne_zero_xzcharts

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

theorem solution [IsDomain R] [IsNoetherianRing R] [W.IsElliptic]
    (i j : Fin 3) (hi : i ≠ 1) (hj : j ≠ 1) :
    ∃ l, kw_lrSixU W i j l ≠ 0 := by
  clear hi hj
  haveI : IsDomain ((𝒜 i) ⊗[R] (𝒜 j)) := isDomain_chartTensor_of_isElliptic W i j
  have hΔF : algebraMap R (FractionRing ((𝒜 i) ⊗[R] (𝒜 j))) W.Δ ≠ 0 :=
    (W.isUnit_Δ.map _).ne_zero
  let ψᵢ : (𝒜 i) →ₐ[R] FractionRing ((𝒜 i) ⊗[R] (𝒜 j)) :=
    (IsScalarTower.toAlgHom R ((𝒜 i) ⊗[R] (𝒜 j)) (FractionRing ((𝒜 i) ⊗[R] (𝒜 j)))).comp
      Algebra.TensorProduct.includeLeft
  let ψⱼ : (𝒜 j) →ₐ[R] FractionRing ((𝒜 i) ⊗[R] (𝒜 j)) :=
    (IsScalarTower.toAlgHom R ((𝒜 i) ⊗[R] (𝒜 j)) (FractionRing ((𝒜 i) ⊗[R] (𝒜 j)))).comp
      Algebra.TensorProduct.includeRight
  have hne := kw_lr_chartTensor_genericProj_pointClass_ne W i j
  obtain ⟨l, hl⟩ :=
    kw_a2_exists_sixU_ne_zero_of_pointClass_ne W (FractionRing ((𝒜 i) ⊗[R] (𝒜 j)))
      hΔF i j ψᵢ ψⱼ hne
  refine ⟨l, ?_⟩

  have hprod : (Algebra.TensorProduct.productMap ψᵢ ψⱼ : ((𝒜 i) ⊗[R] (𝒜 j)) →ₐ[R] _)
      = IsScalarTower.toAlgHom R ((𝒜 i) ⊗[R] (𝒜 j)) (FractionRing ((𝒜 i) ⊗[R] (𝒜 j))) :=
    Algebra.TensorProduct.ext
      (AlgHom.ext fun a => by
        show (Algebra.TensorProduct.productMap ψᵢ ψⱼ) (a ⊗ₜ[R] 1) = ψᵢ a
        rw [Algebra.TensorProduct.productMap_apply_tmul, map_one, mul_one])
      (AlgHom.ext fun b => by
        show (Algebra.TensorProduct.productMap ψᵢ ψⱼ) ((1:(𝒜 i)) ⊗ₜ[R] b) = ψⱼ b
        rw [Algebra.TensorProduct.productMap_apply_tmul, map_one, one_mul])
  intro h
  apply hl
  calc (Algebra.TensorProduct.productMap ψᵢ ψⱼ) (kw_lrSixU W i j l)
      = (IsScalarTower.toAlgHom R ((𝒜 i) ⊗[R] (𝒜 j))
          (FractionRing ((𝒜 i) ⊗[R] (𝒜 j)))) (kw_lrSixU W i j l) :=
        congrFun (congrArg DFunLike.coe hprod) _
    _ = (IsScalarTower.toAlgHom R ((𝒜 i) ⊗[R] (𝒜 j))
          (FractionRing ((𝒜 i) ⊗[R] (𝒜 j)))) 0 := by rw [h]
    _ = 0 := map_zero _

end

end S_WeierstrassProjModel_exists_lrSixU_ne_zero_xzcharts
end P2MW
export P2MW.S_WeierstrassProjModel_exists_lrSixU_ne_zero_xzcharts (solution)
