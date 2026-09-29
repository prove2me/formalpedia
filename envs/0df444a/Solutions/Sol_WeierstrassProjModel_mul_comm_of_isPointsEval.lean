-- Prove2me | solution 1 for WeierstrassProjModel.mul_comm_of_isPointsEval
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/47b26f6b-5d7b-5749-86f4-bb2b0c43f6cb

import Mathlib
import Definitions.Def_WeierstrassCurve_ProjModel
import Theorems.Thm_WeierstrassProjModel_exists_dominant_field_point_selfPullback_of_isElliptic
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassProjModel_mul_comm_of_isPointsEval
p2m_attr_erase "instance" "WeierstrassProjModel.quotGradingSubmoduleDegreeZeroFiniteType WeierstrassProjModel.kw_lrChart_tensorCommRing WeierstrassProjModel.kw_lrChart_biGrading_gradedAlgebra WeierstrassProjModel.projModel_isIso_spec_mapCR WeierstrassProjModel.kw_lrSymOC_isDomain_ℬ₀ WeierstrassProjModel.isProper_projModelStrCR WeierstrassProjModel.homogeneousSubmoduleDegreeZeroFiniteType"
p2m_attr_erase "simp" "WeierstrassProjModel.kw_lrAdd_substHom_X WeierstrassProjModel.kw_lrSym_substHom_X"

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NeronModelInfra WeierstrassProjModel
open scoped WeierstrassCurve.Affine

set_option maxHeartbeats 9600000 in
theorem solution
    (K : Type) [Field K] (W : WeierstrassCurve K) [W.IsElliptic]
    (G : RelativeGroupLaw K (projModelStrCR W.toProjective))
    (ev : ∀ (F : Type) [Field F] [DecidableEq F] [Algebra K F],
      SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap K F)))
          (projModelStrCR W.toProjective) ≃
        (W.toProjective.baseChange F).toAffine.Point)
    (hev : IsPointsEval W.toProjective G ev)
    {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of K))
    (x y : SchemeHomOver t (projModelStrCR W.toProjective)) :
    G.mul t x y = G.mul t y x := by
  classical
  let π := projModelStrCR W.toProjective
  let E2 := pullback π π
  let τ : E2 ⟶ Spec (CommRingCat.of K) := pullback.fst π π ≫ π
  let p₁ : SchemeHomOver τ π := ⟨pullback.fst π π, rfl⟩
  let p₂ : SchemeHomOver τ π := ⟨pullback.snd π π, pullback.condition.symm⟩

  suffices huniv : G.mul τ p₁ p₂ = G.mul τ p₂ p₁ by
    let ψ : T ⟶ E2 := pullback.lift x.1 y.1 (x.2.trans y.2.symm)
    have hψτ : ψ ≫ τ = t := by
      show pullback.lift x.1 y.1 _ ≫ pullback.fst π π ≫ π = t
      rw [pullback.lift_fst_assoc]; exact x.2
    have hψp₁ : schemeHomOverComp ψ hψτ p₁ = x := by
      apply Subtype.ext
      exact pullback.lift_fst _ _ _
    have hψp₂ : schemeHomOverComp ψ hψτ p₂ = y := by
      apply Subtype.ext
      exact pullback.lift_snd _ _ _
    have h1 := G.mul_natural τ t ψ hψτ p₁ p₂
    have h2 := G.mul_natural τ t ψ hψτ p₂ p₁
    rw [hψp₁, hψp₂] at h1 h2
    exact h1.symm.trans (huniv ▸ h2)
  apply Subtype.ext

  haveI hsepπ : IsSeparated π := inferInstance

  obtain ⟨F, instF, instAlg, ι, hdom, halg⟩ :=
    WeierstrassProjModel.exists_dominant_field_point_selfPullback_of_isElliptic K W
  letI : Field F := instF
  letI : Algebra K F := instAlg
  haveI : DecidableEq F := Classical.decEq F
  haveI : IsSchemeTheoreticallyDominant ι := hdom

  have halg' : ι ≫ τ = Spec.map (CommRingCat.ofHom (algebraMap K F)) := halg
  refine WeierstrassProjModel.ext_of_isSchemeTheoreticallyDominant_of_isSeparated π
    ((G.mul τ p₁ p₂).2.trans (G.mul τ p₂ p₁).2.symm) ι ?_

  have hnat1 := G.mul_natural τ _ ι halg' p₁ p₂
  have hnat2 := G.mul_natural τ _ ι halg' p₂ p₁
  set x' := schemeHomOverComp ι halg' p₁
  set y' := schemeHomOverComp ι halg' p₂
  have hcomm_F : G.mul _ x' y' = G.mul _ y' x' := by
    have hadd := hev.1 F
    exact (ev F).injective (by rw [hadd x' y', hadd y' x', add_comm])
  calc ι ≫ (G.mul τ p₁ p₂).1
      = (schemeHomOverComp ι halg' (G.mul τ p₁ p₂)).1 := rfl
    _ = (G.mul _ x' y').1 := by rw [hnat1]
    _ = (G.mul _ y' x').1 := by rw [hcomm_F]
    _ = (schemeHomOverComp ι halg' (G.mul τ p₂ p₁)).1 := by rw [hnat2]
    _ = ι ≫ (G.mul τ p₂ p₁).1 := rfl

end S_WeierstrassProjModel_mul_comm_of_isPointsEval
end P2MW
export P2MW.S_WeierstrassProjModel_mul_comm_of_isPointsEval (solution)
