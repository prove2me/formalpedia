-- Prove2me | solution 1 for WeierstrassProjModel.RelativeGroupLaw.mul_eq_at_id_of_one_eq_at_id_of_isAlgClosed
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/fc08191d-7f17-5492-8d3f-a976298f66c8

import Definitions.Def_WeierstrassCurve_ProjModel
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_AlgebraicGeometry_RelativeGroupLawGrpObj
import Theorems.Thm_WeierstrassProjModel_RelativeGroupLaw_exists_grpObj_eq
import Theorems.Thm_AlgebraicGeometry_GrpObj_mul_eq_of_one_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassProjModel_RelativeGroupLaw_mul_eq_at_id_of_one_eq_at_id_of_isAlgClosed

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.CartesianMonoidalCategory NeronModelInfra GoodReductionJacobian WeierstrassProjModel

universe u

set_option maxHeartbeats 4800000 in
theorem solution
    {K : Type u} [Field K] [IsAlgClosed K] {X : Scheme.{u}}
    (x : X ⟶ Spec (CommRingCat.of K)) [IsProper x] [IsIntegral X]
    [IsReduced ↑(pullback x x)]
    (G₁ G₂ : WeierstrassProjModel.RelativeGroupLaw K x)
    (h : G₁.one (𝟙 _) = G₂.one (𝟙 _)) :
    ∀ P Q : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) x,
      G₁.mul (𝟙 _) P Q = G₂.mul (𝟙 _) P Q := by
  obtain ⟨g₁, hmul₁, hone₁, _⟩ :=
    WeierstrassProjModel.RelativeGroupLaw.exists_grpObj_eq G₁
  obtain ⟨g₂, hmul₂, hone₂, _⟩ :=
    WeierstrassProjModel.RelativeGroupLaw.exists_grpObj_eq G₂

  have ov_inj : ∀ {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of K)}
      {a b : Over.mk t ⟶ Over.mk x},
      overHomToSchemeHomOver a = overHomToSchemeHomOver b → a = b := by
    intro T t a b hab
    first
      | exact overHomToSchemeHomOver_injective hab
      | exact (overHomEquivSchemeHomOver).injective hab
      | { apply Over.OverMorphism.ext
          exact congrArg Subtype.val hab }
      | { ext1; exact congrArg Subtype.val hab }

  have hone : g₁.one = g₂.one := by
    have heq : overHomToSchemeHomOver (toUnit (Over.mk (𝟙 _)) ≫ g₁.one)
        = overHomToSchemeHomOver (toUnit (Over.mk (𝟙 _)) ≫ g₂.one) := by
      rw [hone₁ (𝟙 _), hone₂ (𝟙 _), h]
    have heq' : toUnit (Over.mk (𝟙 _)) ≫ g₁.one
        = toUnit (Over.mk (𝟙 _)) ≫ g₂.one := ov_inj heq

    haveI : IsIso (toUnit (Over.mk (𝟙 (Spec (CommRingCat.of K))))) := by
      first
        | infer_instance
        | exact (Over.mkIdTerminal.uniqueUpToIso
            (isTerminalTensorUnit _)).isIso_hom
        | { refine ⟨Over.mkIdTerminal.from _, ?_, ?_⟩
            · exact Over.mkIdTerminal.hom_ext _ _
            · first
                | exact (isTerminalTensorUnit _).hom_ext _ _
                | exact Subsingleton.elim _ _ }
    exact (cancel_epi (toUnit (Over.mk (𝟙 _)))).mp heq'

  have hmul : g₁.mul = g₂.mul := AlgebraicGeometry.GrpObj.mul_eq_of_one_eq x g₁ g₂ hone

  intro P Q

  obtain ⟨a, ha⟩ : ∃ a, overHomToSchemeHomOver a = P := by
    first
      | exact ⟨schemeHomOverToOverHom P, overHomToSchemeHomOver_schemeHomOverToOverHom P⟩
      | exact ⟨(overHomEquivSchemeHomOver).symm P, (overHomEquivSchemeHomOver).apply_symm_apply P⟩
      | exact ⟨Over.homMk P.1 P.2, Subtype.ext rfl⟩
      | exact ⟨Over.homMk P.1 P.2, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b, overHomToSchemeHomOver b = Q := by
    first
      | exact ⟨schemeHomOverToOverHom Q, overHomToSchemeHomOver_schemeHomOverToOverHom Q⟩
      | exact ⟨(overHomEquivSchemeHomOver).symm Q, (overHomEquivSchemeHomOver).apply_symm_apply Q⟩
      | exact ⟨Over.homMk Q.1 Q.2, Subtype.ext rfl⟩
      | exact ⟨Over.homMk Q.1 Q.2, rfl⟩
  calc G₁.mul (𝟙 _) P Q
      = G₁.mul (𝟙 _) (overHomToSchemeHomOver a) (overHomToSchemeHomOver b) := by rw [ha, hb]
    _ = overHomToSchemeHomOver (lift a b ≫ g₁.mul) := (hmul₁ (𝟙 _) a b).symm
    _ = overHomToSchemeHomOver (lift a b ≫ g₂.mul) := by rw [hmul]
    _ = G₂.mul (𝟙 _) (overHomToSchemeHomOver a) (overHomToSchemeHomOver b) := hmul₂ (𝟙 _) a b
    _ = G₂.mul (𝟙 _) P Q := by rw [ha, hb]

end S_WeierstrassProjModel_RelativeGroupLaw_mul_eq_at_id_of_one_eq_at_id_of_isAlgClosed
end P2MW
export P2MW.S_WeierstrassProjModel_RelativeGroupLaw_mul_eq_at_id_of_one_eq_at_id_of_isAlgClosed (solution)
