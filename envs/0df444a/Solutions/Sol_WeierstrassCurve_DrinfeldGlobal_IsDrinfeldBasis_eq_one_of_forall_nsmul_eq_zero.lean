-- Prove2me | solution 1 for WeierstrassCurve.DrinfeldGlobal.IsDrinfeldBasis.eq_one_of_forall_nsmul_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/c2f09398-9144-5f4d-aea7-a4a55ae228dd

import Mathlib
import Definitions.Def_WeierstrassCurve_ProjModel
import Definitions.Def_WeierstrassCurve_DrinfeldBasisGlobal
import Definitions.Def_WeierstrassCurve_DrinfeldBasisRelative
import Theorems.Thm_WeierstrassProjModel_RelativeGroupLaw_IsDrinfeldBasisOver_exists_comp_fst_schemeKer_eq
import Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_isDrinfeldBasis_iff_isDrinfeldBasisOver_id
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_DrinfeldGlobal_IsDrinfeldBasis_eq_one_of_forall_nsmul_eq_zero

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra WeierstrassProjModel WeierstrassCurve.DrinfeldGlobal

namespace SSqSlotUnique

universe u

section General

variable {R : Type u} [CommRing R] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)}

theorem nsmul_val (G : RelativeGroupLaw R f) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (n : ℕ)
    (x : SchemeHomOver t f) :
    (G.nsmul t n x).1 = x.1 ≫ G.schemeNsmul n := by
  have hx : schemeHomOverComp x.1 x.2 (RelativeGroupLaw.idPoint (f := f)) = x :=
    Subtype.ext (Category.comp_id _)
  have h := G.nsmul_natural f t x.1 x.2 n RelativeGroupLaw.idPoint
  rw [hx] at h
  rw [← h]
  rfl

theorem one_val (G : RelativeGroupLaw R f) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) :
    (G.one t).1 = t ≫ (G.one (𝟙 _)).1 := by
  have h := G.one_natural (𝟙 _) t t (Category.comp_id _)
  exact (congrArg Subtype.val h).symm

theorem nsmul_eq_one_of_exists_comp_fst (G : RelativeGroupLaw R f) (n : ℕ) {T : Scheme.{u}}
    {t : T ⟶ Spec (CommRingCat.of R)} (x : SchemeHomOver t f)
    (hx : ∃ p : T ⟶ G.schemeKer n,
      p ≫ pullback.fst (G.schemeNsmul n) (G.one (𝟙 (Spec (CommRingCat.of R)))).1 = x.1) :
    G.nsmul t n x = G.one t := by
  obtain ⟨p, hp⟩ := hx
  have hsnd : p ≫ pullback.snd (G.schemeNsmul n) (G.one (𝟙 (Spec (CommRingCat.of R)))).1 = t := by
    calc p ≫ pullback.snd (G.schemeNsmul n) (G.one (𝟙 (Spec (CommRingCat.of R)))).1
        = (p ≫ pullback.snd (G.schemeNsmul n) (G.one (𝟙 (Spec (CommRingCat.of R)))).1) ≫
            ((G.one (𝟙 (Spec (CommRingCat.of R)))).1 ≫ f) := by
          rw [(G.one (𝟙 (Spec (CommRingCat.of R)))).2, Category.comp_id]
      _ = p ≫ (pullback.snd (G.schemeNsmul n) (G.one (𝟙 (Spec (CommRingCat.of R)))).1 ≫
            (G.one (𝟙 (Spec (CommRingCat.of R)))).1) ≫ f := by simp only [Category.assoc]
      _ = p ≫ (pullback.fst (G.schemeNsmul n) (G.one (𝟙 (Spec (CommRingCat.of R)))).1 ≫
            G.schemeNsmul n) ≫ f := by rw [pullback.condition]
      _ = (p ≫ pullback.fst (G.schemeNsmul n) (G.one (𝟙 (Spec (CommRingCat.of R)))).1) ≫
            (G.schemeNsmul n ≫ f) := by simp only [Category.assoc]
      _ = x.1 ≫ f := by rw [hp, G.schemeNsmul_over]
      _ = t := x.2
  apply Subtype.ext
  rw [nsmul_val, one_val, ← hp, Category.assoc, pullback.condition, ← Category.assoc, hsnd]

end General

section Eval

variable {K : Type} [Field K] {W : WeierstrassCurve.Projective K}
  {G : RelativeGroupLaw K (projModelStrCR W)}
  {ev : ∀ (F : Type) [Field F] [DecidableEq F] [Algebra K F],
    SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap K F))) (projModelStrCR W) ≃
      (W.baseChange F).toAffine.Point}

theorem ev_one (hev : IsPointsEval W G ev) (F : Type) [Field F] [DecidableEq F] [Algebra K F] :
    ev F (G.one (Spec.map (CommRingCat.ofHom (algebraMap K F)))) = 0 := by
  have h := hev.1 F (G.one _) (G.one _)
  rw [G.one_mul] at h

  have h' : ev F (G.one (Spec.map (CommRingCat.ofHom (algebraMap K F)))) +
      ev F (G.one (Spec.map (CommRingCat.ofHom (algebraMap K F)))) =
      ev F (G.one (Spec.map (CommRingCat.ofHom (algebraMap K F)))) + 0 := by
    rw [add_zero]; exact h.symm
  exact add_left_cancel h'

theorem ev_nsmul (hev : IsPointsEval W G ev) (F : Type) [Field F] [DecidableEq F] [Algebra K F] (n : ℕ)
    (x : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap K F))) (projModelStrCR W)) :
    ev F (G.nsmul _ n x) = n • ev F x := by
  induction n with
  | zero => rw [G.nsmul_zero, zero_smul]; exact ev_one hev F
  | succ n ih => rw [G.nsmul_succ, hev.1, ih, succ_nsmul]

end Eval

section Main

variable {K : Type} [Field K] {W : WeierstrassCurve.Projective K}

theorem id_comp_id_eq_specMap :
    (𝟙 (Spec (CommRingCat.of K)) ≫ 𝟙 (Spec (CommRingCat.of K)) : Spec (CommRingCat.of K) ⟶ _) =
      Spec.map (CommRingCat.ofHom (algebraMap K K)) := by
  rw [Category.comp_id, Algebra.algebraMap_self, CommRingCat.ofHom_id, Spec.map_id]

theorem eq_one_of_nsmul_eq_one [DecidableEq K] (G : RelativeGroupLaw K (projModelStrCR W))
    (ev : ∀ (F : Type) [Field F] [DecidableEq F] [Algebra K F],
      SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap K F))) (projModelStrCR W) ≃
        (W.baseChange F).toAffine.Point)
    (hev : IsPointsEval W G ev) (q : ℕ) (hss : ∀ R : W.toAffine.Point, q • R = 0 → R = 0)
    (P : Section W) (hP : G.nsmul (𝟙 _) q P = G.one (𝟙 _)) :
    P = G.one (𝟙 _) := by

  set P' : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap K K))) (projModelStrCR W) :=
    schemeHomOverComp (𝟙 _) id_comp_id_eq_specMap P with hP'
  have htors : G.nsmul _ q P' = G.one _ := by
    rw [hP', ← G.nsmul_natural (𝟙 _) _ (𝟙 _) id_comp_id_eq_specMap q P, hP, G.one_natural]
  have hq0 : q • ev K P' = 0 := by rw [← ev_nsmul hev K q P', htors, ev_one hev K]
  have hss' : ∀ R : (W.baseChange K).toAffine.Point, q • R = 0 → R = 0 := hss
  have h0 : ev K P' = ev K (G.one _) := by rw [hss' _ hq0, ev_one hev K]
  have h1 : P' = G.one _ := (ev K).injective h0
  apply Subtype.ext
  have h2 := congrArg Subtype.val h1
  rw [hP', schemeHomOverComp_coe, Category.id_comp] at h2
  rw [h2, one_val G (Spec.map (CommRingCat.ofHom (algebraMap K K))), ← id_comp_id_eq_specMap,
    Category.id_comp, Category.id_comp]

end Main

end SSqSlotUnique

open SSqSlotUnique in
theorem solution
    {K : Type} [Field K] [DecidableEq K] (W : WeierstrassCurve.Projective K) (hΔ : IsUnit W.Δ)
    (G : RelativeGroupLaw K (projModelStrCR W))
    (ev : ∀ (F : Type) [Field F] [DecidableEq F] [Algebra K F],
      SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap K F))) (projModelStrCR W) ≃ (W.baseChange F).toAffine.Point)
    (hev : IsPointsEval W G ev)
    (q : ℕ) [Fact q.Prime]

    (hss : ∀ R : W.toAffine.Point, q • R = 0 → R = 0)
    (P Q : Section W) (hPQ : IsDrinfeldBasis G q P Q) :
    P = G.one (𝟙 _) ∧ Q = G.one (𝟙 _) := by
  have hq : 2 ≤ q := (Fact.out : q.Prime).two_le
  have hover : G.IsDrinfeldBasisOver q (𝟙 _) P Q :=
    (WeierstrassCurve.DrinfeldGlobal.isDrinfeldBasis_iff_isDrinfeldBasisOver_id G q P Q).mp hPQ
  obtain ⟨hP, hQ⟩ :=
    WeierstrassProjModel.RelativeGroupLaw.IsDrinfeldBasisOver.exists_comp_fst_schemeKer_eq G hq hover
  exact ⟨eq_one_of_nsmul_eq_one G ev hev q hss P (nsmul_eq_one_of_exists_comp_fst G q P hP),
    eq_one_of_nsmul_eq_one G ev hev q hss Q (nsmul_eq_one_of_exists_comp_fst G q Q hQ)⟩

end S_WeierstrassCurve_DrinfeldGlobal_IsDrinfeldBasis_eq_one_of_forall_nsmul_eq_zero
end P2MW
export P2MW.S_WeierstrassCurve_DrinfeldGlobal_IsDrinfeldBasis_eq_one_of_forall_nsmul_eq_zero (solution)
