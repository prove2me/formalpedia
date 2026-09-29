-- Prove2me | solution 1 for WeierstrassProjModel.mul_comm_of_isPointsEval_domain
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/6931651e-fa70-58c7-bad3-9ad928a38964

import Definitions.Def_WeierstrassCurve_ProjModel
import Theorems.Thm_WeierstrassProjModel_projModelStrCR_isProper
import Theorems.Thm_WeierstrassProjModel_projModelStrCR_smooth
import Theorems.Thm_WeierstrassProjModel_kw_r0_isIntegral_pullbacks
import Theorems.Thm_WeierstrassProjModel_kw_hgi_geometricallyIntegral_of_baseChangeIso
import Theorems.Thm_WeierstrassProjModel_kw_bc_baseChangeIso
import Mathlib.AlgebraicGeometry.FunctionField
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassProjModel_mul_comm_of_isPointsEval_domain
p2m_attr_erase "instance" "WeierstrassProjModel.quotGradingSubmoduleDegreeZeroFiniteType WeierstrassProjModel.kw_lrChart_tensorCommRing WeierstrassProjModel.kw_lrChart_biGrading_gradedAlgebra WeierstrassProjModel.projModel_isIso_spec_mapCR WeierstrassProjModel.kw_lrSymOC_isDomain_ℬ₀ WeierstrassProjModel.isProper_projModelStrCR WeierstrassProjModel.homogeneousSubmoduleDegreeZeroFiniteType"
p2m_attr_erase "simp" "WeierstrassProjModel.kw_lrAdd_substHom_X WeierstrassProjModel.kw_lrSym_substHom_X"

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra WeierstrassProjModel

noncomputable section

namespace SolRowComm

universe u v

private abbrev gj (Y : Scheme.{u}) [IsIntegral Y] : Spec Y.functionField ⟶ Y :=
  Y.fromSpecStalk (genericPoint Y)

private theorem isDominant_gj (Y : Scheme.{u}) [IsIntegral Y] : IsDominant (gj Y) := by
  rw [isDominant_iff, DenseRange, Scheme.range_fromSpecStalk]
  refine Dense.mono (Set.singleton_subset_iff.mpr (specializes_refl _)) ?_
  exact dense_iff_closure_eq.mpr (genericPoint_spec Y)

private scoped instance (Y : Scheme.{u}) [IsIntegral Y] : IsSchemeTheoreticallyDominant (gj Y) := by
  haveI := isDominant_gj Y
  exact IsSchemeTheoreticallyDominant.of_isDominant (gj Y)

variable {R : Type u} [CommRing R] {X : Scheme.{u}} (q : X ⟶ Spec (CommRingCat.of R))

private abbrev ffAlgebra [IsIntegral X] : Algebra R X.functionField :=
  (Spec.preimage (gj X ≫ q)).hom.toAlgebra

private theorem gj_comp [IsIntegral X] :
    letI := ffAlgebra q
    gj X ≫ q = Spec.map (CommRingCat.ofHom (algebraMap R X.functionField)) := by
  letI := ffAlgebra q
  show gj X ≫ q = Spec.map (CommRingCat.ofHom (algebraMap R X.functionField))
  rw [RingHom.algebraMap_toAlgebra, CommRingCat.ofHom_hom, Spec.map_preimage]

variable (m : pullback q q ⟶ X) (hm : m ≫ q = pullback.fst q q ≫ q)

private abbrev addPt {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)}
    (x y : SchemeHomOver t q) : SchemeHomOver t q :=
  ⟨pullback.lift x.1 y.1 (x.2.trans y.2.symm) ≫ m,
    by rw [Category.assoc, hm, pullback.lift_fst_assoc, x.2]⟩

include hm in
private theorem swap_m_eq_m [IsSeparated q] [IsIntegral ↑(pullback q q)]
    [Algebra R (pullback q q).functionField]
    (halg : gj (pullback q q) ≫ pullback.fst q q ≫ q
      = Spec.map (CommRingCat.ofHom (algebraMap R (pullback q q).functionField)))
    {P : Type v} [AddCommGroup P]
    (e : SchemeHomOver
        (Spec.map (CommRingCat.ofHom (algebraMap R (pullback q q).functionField))) q → P)
    (he : Function.Injective e)
    (hmul : ∀ x y, e (addPt q m hm x y) = e x + e y) :
    pullback.lift (pullback.snd q q) (pullback.fst q q) pullback.condition.symm ≫ m = m := by
  let xj : SchemeHomOver
      (Spec.map (CommRingCat.ofHom (algebraMap R (pullback q q).functionField))) q :=
    ⟨gj (pullback q q) ≫ pullback.fst q q, halg⟩
  let yj : SchemeHomOver
      (Spec.map (CommRingCat.ofHom (algebraMap R (pullback q q).functionField))) q :=
    ⟨gj (pullback q q) ≫ pullback.snd q q,
      by rw [Category.assoc, ← pullback.condition]; exact halg⟩
  have key : addPt q m hm yj xj = addPt q m hm xj yj := he (by rw [hmul, hmul, add_comm])
  have hfacL : gj (pullback q q)
        ≫ pullback.lift (pullback.snd q q) (pullback.fst q q) pullback.condition.symm
      = pullback.lift yj.1 xj.1 (yj.2.trans xj.2.symm) := by
    refine pullback.hom_ext ?_ ?_
    · simp only [Category.assoc, pullback.lift_fst, yj]
    · simp only [Category.assoc, pullback.lift_snd, xj]
  have hfacR : gj (pullback q q) = pullback.lift xj.1 yj.1 (xj.2.trans yj.2.symm) := by
    refine pullback.hom_ext ?_ ?_
    · simp only [pullback.lift_fst, xj]
    · simp only [pullback.lift_snd, yj]
  refine ext_of_isSchemeTheoreticallyDominant_of_isSeparated q ?_ (gj (pullback q q)) ?_
  · rw [Category.assoc, hm, pullback.lift_fst_assoc]
    exact pullback.condition.symm
  · rw [← Category.assoc, hfacL]
    conv_rhs => rw [hfacR]
    exact congrArg Subtype.val key

private theorem comm_of_swap
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

section Materialise

variable (G : RelativeGroupLaw R q)

private abbrev fstPt : SchemeHomOver (pullback.fst q q ≫ q) q := ⟨pullback.fst q q, rfl⟩
private abbrev sndPt : SchemeHomOver (pullback.fst q q ≫ q) q :=
  ⟨pullback.snd q q, pullback.condition.symm⟩

private def mulMor : pullback q q ⟶ X :=
  (G.mul (pullback.fst q q ≫ q) (fstPt q) (sndPt q)).1

private theorem mulMor_over : mulMor q G ≫ q = pullback.fst q q ≫ q :=
  (G.mul (pullback.fst q q ≫ q) (fstPt q) (sndPt q)).2

private theorem mul_coe_eq_lift_mulMor {T : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t q) :
    (G.mul t x y).1 = pullback.lift x.1 y.1 (x.2.trans y.2.symm) ≫ mulMor q G := by
  have hψ : pullback.lift x.1 y.1 (x.2.trans y.2.symm) ≫ (pullback.fst q q ≫ q) = t := by
    rw [pullback.lift_fst_assoc, x.2]
  have hnat := G.mul_natural (pullback.fst q q ≫ q) t
    (pullback.lift x.1 y.1 (x.2.trans y.2.symm)) hψ (fstPt q) (sndPt q)
  have hx : schemeHomOverComp (pullback.lift x.1 y.1 (x.2.trans y.2.symm)) hψ (fstPt q) = x :=
    Subtype.ext (pullback.lift_fst _ _ _)
  have hy : schemeHomOverComp (pullback.lift x.1 y.1 (x.2.trans y.2.symm)) hψ (sndPt q) = y :=
    Subtype.ext (pullback.lift_snd _ _ _)
  rw [hx, hy] at hnat
  rw [← hnat, schemeHomOverComp_coe]
  rfl

private theorem addPt_mulMor {T : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t q) :
    addPt q (mulMor q G) (mulMor_over q G) x y = G.mul t x y :=
  Subtype.ext (mul_coe_eq_lift_mulMor q G t x y).symm

end Materialise

private theorem mul_comm_aux (G : RelativeGroupLaw R q) [IsSeparated q]
    [IsIntegral ↑(pullback q q)] [Algebra R (pullback q q).functionField]
    (halg : gj (pullback q q) ≫ pullback.fst q q ≫ q
      = Spec.map (CommRingCat.ofHom (algebraMap R (pullback q q).functionField)))
    {P : Type v} [AddCommGroup P]
    (e : SchemeHomOver
        (Spec.map (CommRingCat.ofHom (algebraMap R (pullback q q).functionField))) q → P)
    (he : Function.Injective e)
    (hmul : ∀ x y, e (G.mul _ x y) = e x + e y)
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t q) :
    G.mul t x y = G.mul t y x := by
  have huniv : pullback.lift (pullback.snd q q) (pullback.fst q q) pullback.condition.symm
      ≫ mulMor q G = mulMor q G :=
    swap_m_eq_m q (mulMor q G) (mulMor_over q G) halg e he
      (fun P Q => by rw [addPt_mulMor]; exact hmul P Q)
  have h := comm_of_swap q (mulMor q G) (mulMor_over q G) huniv t x y
  rw [addPt_mulMor, addPt_mulMor] at h
  exact Subtype.ext h

end SolRowComm
p2m_reactivate "P2MW.S_WeierstrassProjModel_mul_comm_of_isPointsEval_domain.SolRowComm"

end
p2m_reactivate "P2MW.S_WeierstrassProjModel_mul_comm_of_isPointsEval_domain.SolRowComm"

open SolRowComm in
set_option maxSynthPendingDepth 3 in
theorem solution
    {R : Type} [CommRing R] [IsDomain R] [IsNoetherianRing R]
    (W : WeierstrassCurve R) [W.IsElliptic]
    (G : RelativeGroupLaw R (projModelStrCR W.toProjective))
    (ev : ∀ (F : Type) [Field F] [DecidableEq F] [Algebra R F],
      SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R F))) (projModelStrCR W.toProjective) ≃
        (W.toProjective.baseChange F).toAffine.Point)
    (hev : IsPointsEval W.toProjective G ev)
    {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R))
    (x y : SchemeHomOver t (projModelStrCR W.toProjective)) : G.mul t x y = G.mul t y x := by

  have hsm : Smooth (projModelStrCR W.toProjective) := projModelStrCR_smooth W.toProjective
  have hgi : GeometricallyIntegral (projModelStrCR W.toProjective) :=
    kw_hgi_geometricallyIntegral_of_baseChangeIso W (kw_bc_baseChangeIso W)
  haveI : IsProper (projModelStrCR W.toProjective) := projModelStrCR_isProper W.toProjective
  haveI hsep : IsSeparated (projModelStrCR W.toProjective) := IsProper.toIsSeparated
  haveI hE2 : IsIntegral
      ↑(pullback (projModelStrCR W.toProjective) (projModelStrCR W.toProjective)) :=
    (kw_r0_isIntegral_pullbacks W hsm hgi).2.1

  letI hA : Algebra R (pullback (projModelStrCR W.toProjective)
      (projModelStrCR W.toProjective)).functionField :=
    ffAlgebra (pullback.fst (projModelStrCR W.toProjective) (projModelStrCR W.toProjective)
      ≫ projModelStrCR W.toProjective)
  have halg : gj (pullback (projModelStrCR W.toProjective) (projModelStrCR W.toProjective))
        ≫ pullback.fst (projModelStrCR W.toProjective) (projModelStrCR W.toProjective)
        ≫ projModelStrCR W.toProjective
      = Spec.map (CommRingCat.ofHom (algebraMap R
          (pullback (projModelStrCR W.toProjective)
            (projModelStrCR W.toProjective)).functionField)) := by
    have := gj_comp (X := ↑(pullback (projModelStrCR W.toProjective)
      (projModelStrCR W.toProjective)))
      (pullback.fst (projModelStrCR W.toProjective) (projModelStrCR W.toProjective)
        ≫ projModelStrCR W.toProjective)
    rwa [← Category.assoc] at this
  haveI : DecidableEq (pullback (projModelStrCR W.toProjective)
      (projModelStrCR W.toProjective)).functionField := Classical.decEq _

  have key : G.mul t x y = G.mul t y x := by
    refine @mul_comm_aux R _ _ (projModelStrCR W.toProjective) G hsep hE2 hA halg
      _ _ (fun p => ev _ p) (ev _).injective ?_ T t x y
    intro P Q
    exact hev.1 _ P Q
  exact key

end S_WeierstrassProjModel_mul_comm_of_isPointsEval_domain
end P2MW
export P2MW.S_WeierstrassProjModel_mul_comm_of_isPointsEval_domain (solution)
