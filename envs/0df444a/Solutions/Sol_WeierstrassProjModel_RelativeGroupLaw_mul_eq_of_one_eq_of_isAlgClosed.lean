-- Prove2me | solution 1 for WeierstrassProjModel.RelativeGroupLaw.mul_eq_of_one_eq_of_isAlgClosed
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/e640c84d-0e20-55a3-85b9-665f68baed28

import Definitions.Def_WeierstrassCurve_ProjModel_GroupLawVocabulary
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Theorems.Thm_WeierstrassProjModel_RelativeGroupLaw_exists_pullback_snd_schemeHomOverEquiv
import Theorems.Thm_WeierstrassProjModel_RelativeGroupLaw_mul_eq_at_id_of_one_eq_at_id_of_isAlgClosed
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassProjModel_RelativeGroupLaw_mul_eq_of_one_eq_of_isAlgClosed
p2m_attr_erase "simp" "GoodReductionJacobian.relativeGroupLawOfGrpObj_inv GoodReductionJacobian.relativeGroupLawOfGrpObj_mul GoodReductionJacobian.overHomEquivSchemeHomOver_apply_coe GoodReductionJacobian.relativeGroupLawOfGrpObj_one GoodReductionJacobian.overHomEquivSchemeHomOver_symm_apply_left"

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NeronModelInfra GoodReductionJacobian WeierstrassProjModel

universe u

set_option maxHeartbeats 3200000 in
theorem solution
    {R : Type u} [CommRing R] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)}
    (K : Type u) [Field K] [IsAlgClosed K] [Algebra R K]
    [IsProper (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R K))))]
    [IsIntegral ↑(pullback f (Spec.map (CommRingCat.ofHom (algebraMap R K))))]
    [IsReduced ↑(pullback
      (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R K))))
      (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R K)))))]
    (G₁ G₂ : WeierstrassProjModel.RelativeGroupLaw R f)
    (h : G₁.one (Spec.map (CommRingCat.ofHom (algebraMap R K)))
        = G₂.one (Spec.map (CommRingCat.ofHom (algebraMap R K)))) :
    ∀ P Q : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R K))) f,
      G₁.mul (Spec.map (CommRingCat.ofHom (algebraMap R K))) P Q
        = G₂.mul (Spec.map (CommRingCat.ofHom (algebraMap R K))) P Q := by

  obtain ⟨σ, hσ⟩ :=
    WeierstrassProjModel.RelativeGroupLaw.exists_pullback_snd_schemeHomOverEquiv
      (R := R) (f := f) K
  obtain ⟨G₁', hG₁mul, hG₁one⟩ := hσ G₁
  obtain ⟨G₂', hG₂mul, hG₂one⟩ := hσ G₂

  have hone' : G₁'.one (𝟙 _) = G₂'.one (𝟙 _) := by rw [← hG₁one, ← hG₂one, h]

  have hmul' :=
    WeierstrassProjModel.RelativeGroupLaw.mul_eq_at_id_of_one_eq_at_id_of_isAlgClosed
      (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R K)))) G₁' G₂' hone'

  intro P Q
  apply σ.injective
  rw [hG₁mul P Q, hG₂mul P Q]
  exact hmul' (σ P) (σ Q)

end S_WeierstrassProjModel_RelativeGroupLaw_mul_eq_of_one_eq_of_isAlgClosed
end P2MW
export P2MW.S_WeierstrassProjModel_RelativeGroupLaw_mul_eq_of_one_eq_of_isAlgClosed (solution)
