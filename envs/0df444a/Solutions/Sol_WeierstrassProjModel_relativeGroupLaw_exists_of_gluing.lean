-- Prove2me | solution 1 for WeierstrassProjModel.relativeGroupLaw_exists_of_gluing
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/30390d2f-1791-5218-980b-80458c62d369

import Definitions.Def_WeierstrassCurve_ProjModel
import Definitions.Def_WeierstrassCurve_ProjModel_AddFormulas
import Definitions.Def_WeierstrassCurve_ProjModel_GroupLawVocabulary
import Theorems.Thm_WeierstrassProjModel_addMorphism_over
import Theorems.Thm_WeierstrassProjModel_negMor_over
import Theorems.Thm_WeierstrassProjModel_addMorphism_zeroSect_mul
import Theorems.Thm_WeierstrassProjModel_addMorphism_mul_zeroSect
import Theorems.Thm_WeierstrassProjModel_addMorphism_negMor_mul
import Theorems.Thm_WeierstrassProjModel_addMorphism_assoc
import Theorems.Thm_WeierstrassProjModel_addMorphism_comm
import Mathlib.AlgebraicGeometry.FunctionField
import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
import Mathlib.AlgebraicGeometry.Geometrically.Integral
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassProjModel_relativeGroupLaw_exists_of_gluing

set_option Elab.async false

section MEGA_prelude_a2_lean

end MEGA_prelude_a2_lean

section MEGA_DensityKit_lean

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace WeierstrassProjModel
p2m_export "WeierstrassProjModel" "RelativeGroupLaw projModelCR projModelStrCR KwLRSixUCoverage KwLRPerChartCompat KwLROuterCompat kw_lrAddMorphism kw_lrAddNegDiag_negMor kwZeroSect addMorphism_over negMor_over addMorphism_zeroSect_mul addMorphism_mul_zeroSect addMorphism_negMor_mul addMorphism_assoc addMorphism_comm"
namespace Density
p2m_open "WeierstrassProjModel"

universe u

section Integral

variable {R : Type u} [CommRing R] [IsDomain R] [IsNoetherianRing R] {X : Scheme.{u}}

end Integral

section GenericPoint

variable (X : Scheme.{u}) [IsIntegral X]

abbrev genericInclusion : Spec X.functionField ⟶ X :=
  X.fromSpecStalk (genericPoint X)

theorem isDominant_genericInclusion : IsDominant (genericInclusion X) := by
  rw [isDominant_iff, DenseRange, Scheme.range_fromSpecStalk]
  refine Dense.mono (Set.singleton_subset_iff.mpr (specializes_refl _)) ?_
  exact dense_iff_closure_eq.mpr (genericPoint_spec X)

scoped instance isSchemeTheoreticallyDominant_genericInclusion :
    IsSchemeTheoreticallyDominant (genericInclusion X) := by
  haveI := isDominant_genericInclusion X
  exact IsSchemeTheoreticallyDominant.of_isDominant (genericInclusion X)

variable {X} {R : Type u} [CommRing R] (q : X ⟶ Spec (CommRingCat.of R))

end GenericPoint

end WeierstrassProjModel.Density
p2m_reactivate "P2MW.S_WeierstrassProjModel_relativeGroupLaw_exists_of_gluing.WeierstrassProjModel P2MW.S_WeierstrassProjModel_relativeGroupLaw_exists_of_gluing.WeierstrassProjModel.Density"
p2m_reactivate "P2MW.S_WeierstrassProjModel_relativeGroupLaw_exists_of_gluing.WeierstrassProjModel"

end
p2m_reactivate "P2MW.S_WeierstrassProjModel_relativeGroupLaw_exists_of_gluing.WeierstrassProjModel P2MW.S_WeierstrassProjModel_relativeGroupLaw_exists_of_gluing.WeierstrassProjModel.Density"

end MEGA_DensityKit_lean
p2m_reactivate "P2MW.S_WeierstrassProjModel_relativeGroupLaw_exists_of_gluing.WeierstrassProjModel P2MW.S_WeierstrassProjModel_relativeGroupLaw_exists_of_gluing.WeierstrassProjModel.Density"

section MEGA_DensityIdentities_lean

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NeronModelInfra

namespace WeierstrassProjModel
p2m_export "WeierstrassProjModel" "RelativeGroupLaw projModelCR projModelStrCR KwLRSixUCoverage KwLRPerChartCompat KwLROuterCompat kw_lrAddMorphism kw_lrAddNegDiag_negMor kwZeroSect addMorphism_over negMor_over addMorphism_zeroSect_mul addMorphism_mul_zeroSect addMorphism_negMor_mul addMorphism_assoc addMorphism_comm"
namespace Density
p2m_open "WeierstrassProjModel"

universe u v

variable {R : Type u} [CommRing R] {X : Scheme.{u}} (q : X ⟶ Spec (CommRingCat.of R))

section Points

variable (m : pullback q q ⟶ X) (hm : m ≫ q = pullback.fst q q ≫ q)

abbrev addPt {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)} (x y : SchemeHomOver t q) :
    SchemeHomOver t q :=
  ⟨pullback.lift x.1 y.1 (x.2.trans y.2.symm) ≫ m,
    by rw [Category.assoc, hm, pullback.lift_fst_assoc, x.2]⟩

variable (o : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) q)

abbrev onePt {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) : SchemeHomOver t q :=
  ⟨t ≫ o.1, by rw [Category.assoc, o.2, Category.comp_id]⟩

variable (i : X ⟶ X) (hi : i ≫ q = q)

abbrev invPt {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)} (x : SchemeHomOver t q) :
    SchemeHomOver t q :=
  ⟨x.1 ≫ i, by rw [Category.assoc, hi, x.2]⟩

theorem unit_id_cond : (q ≫ o.1) ≫ q = 𝟙 X ≫ q := by
  rw [Category.assoc, o.2, Category.comp_id, Category.id_comp]

include hi in

theorem inv_id_cond : i ≫ q = 𝟙 X ≫ q := by
  rw [hi, Category.id_comp]

end Points
p2m_reactivate "P2MW.S_WeierstrassProjModel_relativeGroupLaw_exists_of_gluing.WeierstrassProjModel P2MW.S_WeierstrassProjModel_relativeGroupLaw_exists_of_gluing.WeierstrassProjModel.Density"

section Triple

variable (m : pullback q q ⟶ X) (hm : m ≫ q = pullback.fst q q ≫ q)

abbrev X3 : Scheme.{u} := pullback (pullback.fst q q ≫ q) q

abbrev fst₃ : X3 q ⟶ pullback q q := pullback.fst (pullback.fst q q ≫ q) q

abbrev snd₃ : X3 q ⟶ X := pullback.snd (pullback.fst q q ≫ q) q

theorem pr₂_over : (fst₃ q ≫ pullback.snd q q) ≫ q = snd₃ q ≫ q :=
  (Category.assoc _ _ _).trans
    ((congrArg (_ ≫ ·) pullback.condition.symm).trans pullback.condition)

def mulLLift : X3 q ⟶ pullback q q :=
  pullback.lift (fst₃ q ≫ m) (snd₃ q)
    (by rw [Category.assoc, hm]; exact pullback.condition)

abbrev mulL : X3 q ⟶ X := mulLLift q m hm ≫ m

def mulRLift : X3 q ⟶ pullback q q :=
  pullback.lift (fst₃ q ≫ pullback.fst q q)
    (pullback.lift (fst₃ q ≫ pullback.snd q q) (snd₃ q) (pr₂_over q) ≫ m)
    (by rw [Category.assoc, Category.assoc, hm, pullback.lift_fst_assoc, Category.assoc]
        exact congrArg (_ ≫ ·) pullback.condition)

abbrev mulR : X3 q ⟶ X := mulRLift q m hm ≫ m

end Triple
p2m_reactivate "P2MW.S_WeierstrassProjModel_relativeGroupLaw_exists_of_gluing.WeierstrassProjModel P2MW.S_WeierstrassProjModel_relativeGroupLaw_exists_of_gluing.WeierstrassProjModel.Density"

section Identities

variable {q} [IsSeparated q] (m : pullback q q ⟶ X) (hm : m ≫ q = pullback.fst q q ≫ q)
  {P : Type v} [AddCommGroup P]

end Identities
p2m_reactivate "P2MW.S_WeierstrassProjModel_relativeGroupLaw_exists_of_gluing.WeierstrassProjModel P2MW.S_WeierstrassProjModel_relativeGroupLaw_exists_of_gluing.WeierstrassProjModel.Density"

section Yoneda

variable {q} (m : pullback q q ⟶ X) (hm : m ≫ q = pullback.fst q q ≫ q)
  (o : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) q)

theorem one_mul_of_univ (huniv : pullback.lift (q ≫ o.1) (𝟙 X) (unit_id_cond q o) ≫ m = 𝟙 X)
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x : SchemeHomOver t q) :
    (addPt q m hm (onePt q o t) x).1 = x.1 := by
  have hfact : pullback.lift (onePt q o t).1 x.1 ((onePt q o t).2.trans x.2.symm)
      = x.1 ≫ pullback.lift (q ≫ o.1) (𝟙 X) (unit_id_cond q o) := by
    refine pullback.hom_ext ?_ ?_
    · simp only [pullback.lift_fst, Category.assoc, ← x.2]
    · simp only [Category.assoc, pullback.lift_snd, Category.comp_id]
  show pullback.lift _ _ _ ≫ m = x.1
  rw [hfact, Category.assoc, huniv, Category.comp_id]

theorem mul_one_of_univ
    (huniv : pullback.lift (𝟙 X) (q ≫ o.1) (unit_id_cond q o).symm ≫ m = 𝟙 X)
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x : SchemeHomOver t q) :
    (addPt q m hm x (onePt q o t)).1 = x.1 := by
  have hfact : pullback.lift x.1 (onePt q o t).1 (x.2.trans (onePt q o t).2.symm)
      = x.1 ≫ pullback.lift (𝟙 X) (q ≫ o.1) (unit_id_cond q o).symm := by
    refine pullback.hom_ext ?_ ?_
    · simp only [Category.assoc, pullback.lift_fst, Category.comp_id]
    · simp only [pullback.lift_snd, Category.assoc, ← x.2]
  show pullback.lift _ _ _ ≫ m = x.1
  rw [hfact, Category.assoc, huniv, Category.comp_id]

theorem inv_mul_of_univ (i : X ⟶ X) (hi : i ≫ q = q)
    (huniv : pullback.lift i (𝟙 X) (inv_id_cond q i hi) ≫ m = q ≫ o.1)
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x : SchemeHomOver t q) :
    (addPt q m hm (invPt q i hi x) x).1 = (onePt q o t).1 := by
  have hfact : pullback.lift (invPt q i hi x).1 x.1 ((invPt q i hi x).2.trans x.2.symm)
      = x.1 ≫ pullback.lift i (𝟙 X) (inv_id_cond q i hi) := by
    refine pullback.hom_ext ?_ ?_
    · simp only [Category.assoc, pullback.lift_fst]
    · simp only [Category.assoc, pullback.lift_snd, Category.comp_id]
  show pullback.lift _ _ _ ≫ m = t ≫ o.1
  rw [hfact, Category.assoc, huniv, ← Category.assoc, x.2]

theorem assoc_of_univ (huniv : mulL q m hm = mulR q m hm)
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x y z : SchemeHomOver t q) :
    (addPt q m hm (addPt q m hm x y) z).1 = (addPt q m hm x (addPt q m hm y z)).1 := by
  let xyz : T ⟶ X3 q :=
    pullback.lift (pullback.lift x.1 y.1 (x.2.trans y.2.symm)) z.1
      (by rw [pullback.lift_fst_assoc, x.2, z.2])
  have hfactL : pullback.lift (pullback.lift x.1 y.1 (x.2.trans y.2.symm) ≫ m) z.1
        ((addPt q m hm x y).2.trans z.2.symm)
      = xyz ≫ mulLLift q m hm := by
    refine pullback.hom_ext ?_ ?_
    · simp only [mulLLift, xyz, Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc]
    · simp only [mulLLift, xyz, Category.assoc, pullback.lift_snd]
  have hfactR : pullback.lift x.1 (pullback.lift y.1 z.1 (y.2.trans z.2.symm) ≫ m)
        (x.2.trans (addPt q m hm y z).2.symm)
      = xyz ≫ mulRLift q m hm := by
    refine pullback.hom_ext ?_ ?_
    · simp only [mulRLift, xyz, Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc]
    · simp only [mulRLift, Category.assoc, pullback.lift_snd]
      refine (congrArg (· ≫ m) (pullback.hom_ext ?_ ?_)).trans (Category.assoc _ _ _)
      · simp only [xyz, Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc,
          pullback.lift_snd]
      · simp only [xyz, Category.assoc, pullback.lift_snd]
  show pullback.lift _ _ _ ≫ m = pullback.lift _ _ _ ≫ m
  calc  pullback.lift (pullback.lift x.1 y.1 (x.2.trans y.2.symm) ≫ m) z.1 _ ≫ m
      = (xyz ≫ mulLLift q m hm) ≫ m := congrArg (· ≫ m) hfactL
    _ = xyz ≫ mulL q m hm := Category.assoc _ _ _
    _ = xyz ≫ mulR q m hm := congrArg (xyz ≫ ·) huniv
    _ = (xyz ≫ mulRLift q m hm) ≫ m := (Category.assoc _ _ _).symm
    _ = pullback.lift x.1 (pullback.lift y.1 z.1 (y.2.trans z.2.symm) ≫ m) _ ≫ m :=
        (congrArg (· ≫ m) hfactR).symm

theorem comm_of_univ
    (huniv : pullback.lift (pullback.snd q q) (pullback.fst q q) pullback.condition.symm ≫ m = m)
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t q) :
    (addPt q m hm x y).1 = (addPt q m hm y x).1 := by
  have hfact : pullback.lift x.1 y.1 (x.2.trans y.2.symm)
      = pullback.lift y.1 x.1 (y.2.trans x.2.symm)
          ≫ pullback.lift (pullback.snd q q) (pullback.fst q q) pullback.condition.symm := by
    refine pullback.hom_ext ?_ ?_
    · simp only [Category.assoc, pullback.lift_fst, pullback.lift_snd]
    · simp only [Category.assoc, pullback.lift_snd, pullback.lift_fst]
  show pullback.lift _ _ _ ≫ m = pullback.lift _ _ _ ≫ m
  rw [hfact, Category.assoc, huniv]

end Yoneda
p2m_reactivate "P2MW.S_WeierstrassProjModel_relativeGroupLaw_exists_of_gluing.WeierstrassProjModel P2MW.S_WeierstrassProjModel_relativeGroupLaw_exists_of_gluing.WeierstrassProjModel.Density"

end WeierstrassProjModel.Density
p2m_reactivate "P2MW.S_WeierstrassProjModel_relativeGroupLaw_exists_of_gluing.WeierstrassProjModel P2MW.S_WeierstrassProjModel_relativeGroupLaw_exists_of_gluing.WeierstrassProjModel.Density"
p2m_reactivate "P2MW.S_WeierstrassProjModel_relativeGroupLaw_exists_of_gluing.WeierstrassProjModel P2MW.S_WeierstrassProjModel_relativeGroupLaw_exists_of_gluing.WeierstrassProjModel.Density"

end
p2m_reactivate "P2MW.S_WeierstrassProjModel_relativeGroupLaw_exists_of_gluing.WeierstrassProjModel P2MW.S_WeierstrassProjModel_relativeGroupLaw_exists_of_gluing.WeierstrassProjModel.Density"

end MEGA_DensityIdentities_lean
p2m_reactivate "P2MW.S_WeierstrassProjModel_relativeGroupLaw_exists_of_gluing.WeierstrassProjModel P2MW.S_WeierstrassProjModel_relativeGroupLaw_exists_of_gluing.WeierstrassProjModel.Density"

section MEGA_SolShims

noncomputable section

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra WeierstrassProjModel P2MW.S_WeierstrassProjModel_relativeGroupLaw_exists_of_gluing.WeierstrassProjModel"

namespace WeierstrassProjModel
p2m_export "WeierstrassProjModel" "RelativeGroupLaw projModelCR projModelStrCR KwLRSixUCoverage KwLRPerChartCompat KwLROuterCompat kw_lrAddMorphism kw_lrAddNegDiag_negMor kwZeroSect addMorphism_over negMor_over addMorphism_zeroSect_mul addMorphism_mul_zeroSect addMorphism_negMor_mul addMorphism_assoc addMorphism_comm"
p2m_open "WeierstrassProjModel"

universe u

variable {R : Type u} [CommRing R]

theorem kw_lrAddMorphism_over (W : WeierstrassCurve R)
    (hcov : KwLRSixUCoverage W) (hcompat : KwLRPerChartCompat W) (houter : KwLROuterCompat W) :
    kw_lrAddMorphism W hcov hcompat houter ≫ projModelStrCR W.toProjective = pullback.fst (projModelStrCR W.toProjective) (projModelStrCR W.toProjective) ≫ projModelStrCR W.toProjective :=
  WeierstrassProjModel.addMorphism_over W hcov hcompat houter

theorem kw_lrAddNegDiag_negMor_over (W : WeierstrassCurve R) :
    kw_lrAddNegDiag_negMor W ≫ projModelStrCR W.toProjective = projModelStrCR W.toProjective :=
  WeierstrassProjModel.negMor_over W

section Laws

variable [IsDomain R] [IsNoetherianRing R] (W : WeierstrassCurve R)
  (hsm : Smooth (projModelStrCR W.toProjective)) (hgi : GeometricallyIntegral (projModelStrCR W.toProjective)) (hΔ : IsUnit W.Δ)
  (hcov : KwLRSixUCoverage W) (hcompat : KwLRPerChartCompat W) (houter : KwLROuterCompat W)

include hsm hgi hΔ in

theorem kw_lrDens_unitL :
    pullback.lift (projModelStrCR W.toProjective ≫ (kwZeroSect R W).1) (𝟙 (projModelCR W.toProjective))
        (Density.unit_id_cond (projModelStrCR W.toProjective) (kwZeroSect R W)) ≫ kw_lrAddMorphism W hcov hcompat houter = 𝟙 (projModelCR W.toProjective) :=
  WeierstrassProjModel.addMorphism_zeroSect_mul W hsm hgi hΔ hcov hcompat houter

include hsm hgi hΔ in

theorem kw_lrDens_unitR :
    pullback.lift (𝟙 (projModelCR W.toProjective)) (projModelStrCR W.toProjective ≫ (kwZeroSect R W).1)
        (Density.unit_id_cond (projModelStrCR W.toProjective) (kwZeroSect R W)).symm ≫ kw_lrAddMorphism W hcov hcompat houter = 𝟙 (projModelCR W.toProjective) :=
  WeierstrassProjModel.addMorphism_mul_zeroSect W hsm hgi hΔ hcov hcompat houter

include hsm hgi hΔ in

theorem kw_lrDens_assoc :
    Density.mulL (projModelStrCR W.toProjective) (kw_lrAddMorphism W hcov hcompat houter) (kw_lrAddMorphism_over W hcov hcompat houter)
      = Density.mulR (projModelStrCR W.toProjective) (kw_lrAddMorphism W hcov hcompat houter) (kw_lrAddMorphism_over W hcov hcompat houter) :=
  WeierstrassProjModel.addMorphism_assoc W hsm hgi hΔ hcov hcompat houter
    (kw_lrAddMorphism_over W hcov hcompat houter)

include hsm hgi hΔ in

theorem kw_lrDens_comm :
    pullback.lift (pullback.snd (projModelStrCR W.toProjective) (projModelStrCR W.toProjective)) (pullback.fst (projModelStrCR W.toProjective) (projModelStrCR W.toProjective)) pullback.condition.symm
      ≫ kw_lrAddMorphism W hcov hcompat houter = kw_lrAddMorphism W hcov hcompat houter :=
  WeierstrassProjModel.addMorphism_comm W hsm hgi hΔ hcov hcompat houter

end Laws
p2m_reactivate "P2MW.S_WeierstrassProjModel_relativeGroupLaw_exists_of_gluing.WeierstrassProjModel P2MW.S_WeierstrassProjModel_relativeGroupLaw_exists_of_gluing.WeierstrassProjModel.Density"

end WeierstrassProjModel
p2m_reactivate "P2MW.S_WeierstrassProjModel_relativeGroupLaw_exists_of_gluing.WeierstrassProjModel P2MW.S_WeierstrassProjModel_relativeGroupLaw_exists_of_gluing.WeierstrassProjModel.Density"

end
p2m_reactivate "P2MW.S_WeierstrassProjModel_relativeGroupLaw_exists_of_gluing.WeierstrassProjModel P2MW.S_WeierstrassProjModel_relativeGroupLaw_exists_of_gluing.WeierstrassProjModel.Density"

end MEGA_SolShims
p2m_reactivate "P2MW.S_WeierstrassProjModel_relativeGroupLaw_exists_of_gluing.WeierstrassProjModel P2MW.S_WeierstrassProjModel_relativeGroupLaw_exists_of_gluing.WeierstrassProjModel.Density"

section MEGA_KwProjWeierstrassRelGroupLawSupply_lean

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace WeierstrassProjModel
p2m_export "WeierstrassProjModel" "RelativeGroupLaw projModelCR projModelStrCR KwLRSixUCoverage KwLRPerChartCompat KwLROuterCompat kw_lrAddMorphism kw_lrAddNegDiag_negMor kwZeroSect addMorphism_over negMor_over addMorphism_zeroSect_mul addMorphism_mul_zeroSect addMorphism_negMor_mul addMorphism_assoc addMorphism_comm"
p2m_open "WeierstrassProjModel"

p2m_open "WeierstrassProjModel P2MW.S_WeierstrassProjModel_relativeGroupLaw_exists_of_gluing.WeierstrassProjModel"

structure KwProjWeierstrassRelGroupLawSupply (R : Type u) [CommRing R]
    (V : WeierstrassCurve.Projective R) where

  G : RelativeGroupLaw R (projModelStrCR V)

end WeierstrassProjModel
p2m_reactivate "P2MW.S_WeierstrassProjModel_relativeGroupLaw_exists_of_gluing.WeierstrassProjModel P2MW.S_WeierstrassProjModel_relativeGroupLaw_exists_of_gluing.WeierstrassProjModel.Density"

end
p2m_reactivate "P2MW.S_WeierstrassProjModel_relativeGroupLaw_exists_of_gluing.WeierstrassProjModel P2MW.S_WeierstrassProjModel_relativeGroupLaw_exists_of_gluing.WeierstrassProjModel.Density"

end MEGA_KwProjWeierstrassRelGroupLawSupply_lean
p2m_reactivate "P2MW.S_WeierstrassProjModel_relativeGroupLaw_exists_of_gluing.WeierstrassProjModel P2MW.S_WeierstrassProjModel_relativeGroupLaw_exists_of_gluing.WeierstrassProjModel.Density"

section MEGA_KwProjWeierstrassRelGroupLawConstruct_lean

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits WeierstrassCurve

universe u

namespace WeierstrassProjModel
p2m_export "WeierstrassProjModel" "RelativeGroupLaw projModelCR projModelStrCR KwLRSixUCoverage KwLRPerChartCompat KwLROuterCompat kw_lrAddMorphism kw_lrAddNegDiag_negMor kwZeroSect addMorphism_over negMor_over addMorphism_zeroSect_mul addMorphism_mul_zeroSect addMorphism_negMor_mul addMorphism_assoc addMorphism_comm"
p2m_open "WeierstrassProjModel"

p2m_open "WeierstrassProjModel P2MW.S_WeierstrassProjModel_relativeGroupLaw_exists_of_gluing.WeierstrassProjModel NeronModelInfra HomogeneousIdealQuotientGrading"

attribute [local instance] MvPolynomial.gradedAlgebra

variable (R : Type u) [CommRing R]

section ZeroSection

variable (W : WeierstrassCurve R)

end ZeroSection
p2m_reactivate "P2MW.S_WeierstrassProjModel_relativeGroupLaw_exists_of_gluing.WeierstrassProjModel P2MW.S_WeierstrassProjModel_relativeGroupLaw_exists_of_gluing.WeierstrassProjModel.Density"

section AddLawData

variable (W : WeierstrassCurve R)

local notation "E" => projModelCR W.toProjective
local notation "π" => projModelStrCR W.toProjective

structure KwProjWeierstrassAddLawData where

  m : pullback (projModelStrCR W.toProjective) (projModelStrCR W.toProjective)
        ⟶ projModelCR W.toProjective

  m_over : m ≫ projModelStrCR W.toProjective
    = pullback.fst (projModelStrCR W.toProjective) (projModelStrCR W.toProjective)
        ≫ projModelStrCR W.toProjective

  assoc : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
    (x y z : SchemeHomOver t (projModelStrCR W.toProjective)),
    pullback.lift (pullback.lift x.1 y.1 (x.2.trans y.2.symm) ≫ m) z.1
        (by rw [Category.assoc, m_over, pullback.lift_fst_assoc, x.2, z.2]) ≫ m
      = pullback.lift x.1 (pullback.lift y.1 z.1 (y.2.trans z.2.symm) ≫ m)
        (by rw [Category.assoc, m_over, pullback.lift_fst_assoc, y.2, x.2]) ≫ m

  one_mul : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
    (x : SchemeHomOver t (projModelStrCR W.toProjective)),
    pullback.lift (t ≫ (kwZeroSect R W).1) x.1
        (by rw [Category.assoc, (kwZeroSect R W).2, Category.comp_id, x.2]) ≫ m = x.1

  mul_one : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
    (x : SchemeHomOver t (projModelStrCR W.toProjective)),
    pullback.lift x.1 (t ≫ (kwZeroSect R W).1)
        (by rw [Category.assoc, (kwZeroSect R W).2, Category.comp_id, x.2]) ≫ m = x.1

  inv_mul : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
    (x : SchemeHomOver t (projModelStrCR W.toProjective)),
    pullback.lift (x.1 ≫ kw_lrAddNegDiag_negMor W) x.1
        (by rw [Category.assoc, kw_lrAddNegDiag_negMor_over W]) ≫ m = t ≫ (kwZeroSect R W).1

end AddLawData
p2m_reactivate "P2MW.S_WeierstrassProjModel_relativeGroupLaw_exists_of_gluing.WeierstrassProjModel P2MW.S_WeierstrassProjModel_relativeGroupLaw_exists_of_gluing.WeierstrassProjModel.Density"

section Assembly

variable {R} (W : WeierstrassCurve R) (addLaw : KwProjWeierstrassAddLawData R W)

def kwProjWeierstrassRelGroupLawSupply :
    KwProjWeierstrassRelGroupLawSupply R W.toProjective where
  G :=
  { mul := fun t x y => ⟨pullback.lift x.1 y.1 (x.2.trans y.2.symm) ≫ addLaw.m,
      by rw [Category.assoc, addLaw.m_over, pullback.lift_fst_assoc, x.2]⟩
    one := fun t => ⟨t ≫ (kwZeroSect R W).1,
      by rw [Category.assoc, (kwZeroSect R W).2, Category.comp_id]⟩
    inv := fun t x => ⟨x.1 ≫ kw_lrAddNegDiag_negMor W,
      by rw [Category.assoc, kw_lrAddNegDiag_negMor_over W, x.2]⟩
    mul_assoc := fun t x y z => Subtype.ext (addLaw.assoc t x y z)
    one_mul := fun t x => Subtype.ext (addLaw.one_mul t x)
    mul_one := fun t x => Subtype.ext (addLaw.mul_one t x)
    inv_mul_cancel := fun t x => Subtype.ext (addLaw.inv_mul t x)
    mul_natural := fun t t' ψ hψ x y => Subtype.ext <| by
      show ψ ≫ pullback.lift x.1 y.1 _ ≫ addLaw.m
        = pullback.lift (ψ ≫ x.1) (ψ ≫ y.1) _ ≫ addLaw.m
      rw [← Category.assoc]; congr 1
      exact pullback.hom_ext
        (by rw [Category.assoc, pullback.lift_fst, pullback.lift_fst])
        (by rw [Category.assoc, pullback.lift_snd, pullback.lift_snd]) }

end Assembly
p2m_reactivate "P2MW.S_WeierstrassProjModel_relativeGroupLaw_exists_of_gluing.WeierstrassProjModel P2MW.S_WeierstrassProjModel_relativeGroupLaw_exists_of_gluing.WeierstrassProjModel.Density"

end WeierstrassProjModel
p2m_reactivate "P2MW.S_WeierstrassProjModel_relativeGroupLaw_exists_of_gluing.WeierstrassProjModel P2MW.S_WeierstrassProjModel_relativeGroupLaw_exists_of_gluing.WeierstrassProjModel.Density"

end
p2m_reactivate "P2MW.S_WeierstrassProjModel_relativeGroupLaw_exists_of_gluing.WeierstrassProjModel P2MW.S_WeierstrassProjModel_relativeGroupLaw_exists_of_gluing.WeierstrassProjModel.Density"
end MEGA_KwProjWeierstrassRelGroupLawConstruct_lean
p2m_reactivate "P2MW.S_WeierstrassProjModel_relativeGroupLaw_exists_of_gluing.WeierstrassProjModel P2MW.S_WeierstrassProjModel_relativeGroupLaw_exists_of_gluing.WeierstrassProjModel.Density"

section MEGA_WireDensity_lean

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NeronModelInfra

namespace WeierstrassProjModel
p2m_export "WeierstrassProjModel" "RelativeGroupLaw projModelCR projModelStrCR KwLRSixUCoverage KwLRPerChartCompat KwLROuterCompat kw_lrAddMorphism kw_lrAddNegDiag_negMor kwZeroSect addMorphism_over negMor_over addMorphism_zeroSect_mul addMorphism_mul_zeroSect addMorphism_negMor_mul addMorphism_assoc addMorphism_comm"
p2m_open "WeierstrassProjModel"

attribute [local instance] MvPolynomial.gradedAlgebra

universe u

variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

section WireDensity

variable [IsDomain R] [IsNoetherianRing R]
  (hsm : Smooth (projModelStrCR W.toProjective))
  (hgi : GeometricallyIntegral (projModelStrCR W.toProjective))
  (hΔ : IsUnit W.Δ)
  (hcov : KwLRSixUCoverage W) (hcompat : KwLRPerChartCompat W) (houter : KwLROuterCompat W)

set_option quotPrecheck false in
local notation "E" => projModelCR W.toProjective
set_option quotPrecheck false in
local notation "π" => projModelStrCR W.toProjective
set_option quotPrecheck false in
local notation "madd" => kw_lrAddMorphism W hcov hcompat houter

def kw_projWeierstrassAddLawData_density : KwProjWeierstrassAddLawData R W :=
  { m := madd
    m_over := kw_lrAddMorphism_over W hcov hcompat houter
    assoc := fun t x y z =>
      Density.assoc_of_univ madd (kw_lrAddMorphism_over W hcov hcompat houter)
        (kw_lrDens_assoc W hsm hgi hΔ hcov hcompat houter) t x y z
    one_mul := fun t x =>
      Density.one_mul_of_univ madd (kw_lrAddMorphism_over W hcov hcompat houter)
        (kwZeroSect R W) (kw_lrDens_unitL W hsm hgi hΔ hcov hcompat houter) t x
    mul_one := fun t x =>
      Density.mul_one_of_univ madd (kw_lrAddMorphism_over W hcov hcompat houter)
        (kwZeroSect R W) (kw_lrDens_unitR W hsm hgi hΔ hcov hcompat houter) t x
    inv_mul := fun t x =>
      Density.inv_mul_of_univ madd (kw_lrAddMorphism_over W hcov hcompat houter)
        (kwZeroSect R W) (kw_lrAddNegDiag_negMor W) (kw_lrAddNegDiag_negMor_over W)
        (WeierstrassProjModel.addMorphism_negMor_mul W hsm hgi hΔ hcov hcompat houter
          (kw_lrAddNegDiag_negMor_over W)) t x }

def kw_lrRelGroupLawSupply_density : KwProjWeierstrassRelGroupLawSupply R W.toProjective :=
  kwProjWeierstrassRelGroupLawSupply W
    (kw_projWeierstrassAddLawData_density W hsm hgi hΔ hcov hcompat houter)

theorem kw_lrRelGroupLawSupply_density_comm {T : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t π) :
    (kw_lrRelGroupLawSupply_density W hsm hgi hΔ hcov hcompat houter).G.mul t x y
      = (kw_lrRelGroupLawSupply_density W hsm hgi hΔ hcov hcompat houter).G.mul t y x :=
  Subtype.ext (Density.comm_of_univ madd (kw_lrAddMorphism_over W hcov hcompat houter)
    (kw_lrDens_comm W hsm hgi hΔ hcov hcompat houter) t x y)

include hsm hgi hΔ in

theorem kw_lrRelGroupLaw_exists_density :
    ∃ G : WeierstrassProjModel.RelativeGroupLaw R π,
      (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t π),
          (G.mul t x y).1 = pullback.lift x.1 y.1 (x.2.trans y.2.symm) ≫ madd) ∧
      (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)),
          (G.one t).1 = t ≫ (kwZeroSect R W).1) ∧
      (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t π),
          G.mul t x y = G.mul t y x) :=
  ⟨(kw_lrRelGroupLawSupply_density W hsm hgi hΔ hcov hcompat houter).G,
    fun _ _ _ => rfl, fun _ => rfl,
    fun t x y => kw_lrRelGroupLawSupply_density_comm W hsm hgi hΔ hcov hcompat houter t x y⟩

end WireDensity
p2m_reactivate "P2MW.S_WeierstrassProjModel_relativeGroupLaw_exists_of_gluing.WeierstrassProjModel P2MW.S_WeierstrassProjModel_relativeGroupLaw_exists_of_gluing.WeierstrassProjModel.Density"

section Final

variable [IsDomain R] [IsNoetherianRing R] [Invertible (2 : R)]

set_option quotPrecheck false in
local notation "π" => projModelStrCR W.toProjective

end Final
p2m_reactivate "P2MW.S_WeierstrassProjModel_relativeGroupLaw_exists_of_gluing.WeierstrassProjModel P2MW.S_WeierstrassProjModel_relativeGroupLaw_exists_of_gluing.WeierstrassProjModel.Density"

end WeierstrassProjModel
p2m_reactivate "P2MW.S_WeierstrassProjModel_relativeGroupLaw_exists_of_gluing.WeierstrassProjModel P2MW.S_WeierstrassProjModel_relativeGroupLaw_exists_of_gluing.WeierstrassProjModel.Density"

end
p2m_reactivate "P2MW.S_WeierstrassProjModel_relativeGroupLaw_exists_of_gluing.WeierstrassProjModel P2MW.S_WeierstrassProjModel_relativeGroupLaw_exists_of_gluing.WeierstrassProjModel.Density"

end MEGA_WireDensity_lean
p2m_reactivate "P2MW.S_WeierstrassProjModel_relativeGroupLaw_exists_of_gluing.WeierstrassProjModel P2MW.S_WeierstrassProjModel_relativeGroupLaw_exists_of_gluing.WeierstrassProjModel.Density"

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra _root_.WeierstrassProjModel _root_.P2MW.S_WeierstrassProjModel_relativeGroupLaw_exists_of_gluing.WeierstrassProjModel in
theorem solution.{u} {R : Type u} [CommRing R] [IsDomain R]
    [IsNoetherianRing R] (W : WeierstrassCurve R)
    (hsm : Smooth (projModelStrCR W.toProjective))
    (hgi : GeometricallyIntegral (projModelStrCR W.toProjective)) (hΔ : IsUnit W.Δ)
    (hcov : KwLRSixUCoverage W) (hcompat : KwLRPerChartCompat W) (houter : KwLROuterCompat W) :
    ∃ G : WeierstrassProjModel.RelativeGroupLaw R (projModelStrCR W.toProjective),
      (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
          (x y : SchemeHomOver t (projModelStrCR W.toProjective)),
          (G.mul t x y).1 = pullback.lift x.1 y.1 (x.2.trans y.2.symm) ≫ kw_lrAddMorphism W hcov hcompat houter) ∧
      (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)), (G.one t).1 = t ≫ (kwZeroSect R W).1) ∧
      (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
          (x y : SchemeHomOver t (projModelStrCR W.toProjective)), G.mul t x y = G.mul t y x) :=
  WeierstrassProjModel.kw_lrRelGroupLaw_exists_density W hsm hgi hΔ hcov hcompat houter

end S_WeierstrassProjModel_relativeGroupLaw_exists_of_gluing
end P2MW
export P2MW.S_WeierstrassProjModel_relativeGroupLaw_exists_of_gluing (solution)
