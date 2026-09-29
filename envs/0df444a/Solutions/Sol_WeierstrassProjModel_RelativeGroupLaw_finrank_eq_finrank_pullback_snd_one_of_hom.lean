-- Prove2me | solution 1 for WeierstrassProjModel.RelativeGroupLaw.finrank_eq_finrank_pullback_snd_one_of_hom
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/89aa320a-ffc1-5927-b412-f18bf1ae9fc0

import Mathlib.AlgebraicGeometry.Morphisms.FlatRank
import Definitions.Def_WeierstrassCurve_ProjModel
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassProjModel_RelativeGroupLaw_finrank_eq_finrank_pullback_snd_one_of_hom

set_option autoImplicit false

p2m_open "AlgebraicGeometry CategoryTheory CategoryTheory.Limits NeronModelInfra WeierstrassProjModel P2MW.S_WeierstrassProjModel_RelativeGroupLaw_finrank_eq_finrank_pullback_snd_one_of_hom.WeierstrassProjModel"

universe u

noncomputable section

namespace WeierstrassProjModel
p2m_export "WeierstrassProjModel" "schemeHomOverComp schemeHomOverComp_coe RelativeGroupLaw"
namespace RelativeGroupLaw
p2m_export "WeierstrassProjModel.RelativeGroupLaw" "pointGroup one_natural mul_one inv_mul_cancel one_mul inv mul mul_natural one"
namespace HomFinrankAux
p2m_open "WeierstrassProjModel.RelativeGroupLaw WeierstrassProjModel"

variable {R : Type u} [CommRing R]

section GroupFacts

variable {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)} (G : RelativeGroupLaw R f)
  {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))

theorem eq_one_of_mul_self (x : SchemeHomOver t f) (h : G.mul t x x = x) : x = G.one t := by
  letI := G.pointGroup t
  have h' : x * x = x * 1 := by rw [_root_.mul_one]; exact h
  exact mul_left_cancel h'

theorem eq_inv_of_mul_eq_one (x y : SchemeHomOver t f) (h : G.mul t x y = G.one t) :
    x = G.inv t y := by
  letI := G.pointGroup t
  exact eq_inv_of_mul_eq_one_left h

theorem mul_inv_cancel' (x : SchemeHomOver t f) : G.mul t x (G.inv t x) = G.one t := by
  letI := G.pointGroup t
  exact mul_inv_cancel x

theorem mul_inv_cancel_right' (x y : SchemeHomOver t f) :
    G.mul t (G.mul t x y) (G.inv t y) = x := by
  letI := G.pointGroup t
  exact mul_inv_cancel_right x y

theorem inv_mul_cancel_right' (x y : SchemeHomOver t f) :
    G.mul t (G.mul t x (G.inv t y)) y = x := by
  letI := G.pointGroup t
  exact inv_mul_cancel_right x y

theorem one_coe : (G.one t).1 = t ≫ (G.one (𝟙 _)).1 := by
  have h := G.one_natural (𝟙 _) t t (Category.comp_id t)
  rw [← h, schemeHomOverComp_coe]

theorem inv_natural {T' : Scheme.{u}} (t' : T' ⟶ Spec (CommRingCat.of R)) (ψ : T' ⟶ T)
    (hψ : ψ ≫ t = t') (x : SchemeHomOver t f) :
    schemeHomOverComp ψ hψ (G.inv t x) = G.inv t' (schemeHomOverComp ψ hψ x) := by
  apply eq_inv_of_mul_eq_one
  rw [← G.mul_natural, G.inv_mul_cancel, G.one_natural]

end GroupFacts

variable {A B : Scheme.{u}}
  {fA : A ⟶ Spec (CommRingCat.of R)} {fB : B ⟶ Spec (CommRingCat.of R)}
  (LA : RelativeGroupLaw R fA) (LB : RelativeGroupLaw R fB)
  (p : A ⟶ B) (hp : p ≫ fB = fA)

def pushPt {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)} (x : SchemeHomOver t fA) :
    SchemeHomOver t fB :=
  ⟨x.1 ≫ p, by rw [Category.assoc, hp]; exact x.2⟩

@[scoped simp] theorem pushPt_coe {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)}
    (x : SchemeHomOver t fA) : (pushPt p hp x).1 = x.1 ≫ p := rfl

def IsHom : Prop :=
  ∀ {S : Scheme.{u}} (t : S ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t fA),
    pushPt p hp (LA.mul t x y) = LB.mul t (pushPt p hp x) (pushPt p hp y)

variable {LA LB p hp}

theorem IsHom.pushPt_one (H : IsHom LA LB p hp) {T : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of R)) : pushPt p hp (LA.one t) = LB.one t := by
  apply eq_one_of_mul_self
  rw [← H, LA.one_mul]

theorem IsHom.pushPt_inv (H : IsHom LA LB p hp) {T : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of R)) (x : SchemeHomOver t fA) :
    pushPt p hp (LA.inv t x) = LB.inv t (pushPt p hp x) := by
  apply eq_inv_of_mul_eq_one
  rw [← H, LA.inv_mul_cancel, H.pushPt_one]

variable (LA LB p hp)

abbrev unitSec : Spec (CommRingCat.of R) ⟶ B := (LB.one (𝟙 _)).1

theorem unitSec_comp : unitSec LB ≫ fB = 𝟙 _ := (LB.one (𝟙 _)).2

def xP : SchemeHomOver (pullback.snd p p ≫ fA) fA :=
  ⟨pullback.fst p p, by
    have h : pullback.fst p p ≫ p ≫ fB = pullback.snd p p ≫ p ≫ fB := by
      rw [pullback.condition_assoc]
    simpa only [hp] using h⟩

def yP : SchemeHomOver (pullback.snd p p ≫ fA) fA :=
  ⟨pullback.snd p p, rfl⟩

def mP : SchemeHomOver (pullback.snd p p ≫ fA) fA :=
  LA.mul _ (xP p hp) (LA.inv _ (yP p))

theorem pushPt_xP : pushPt p hp (xP p hp) = pushPt p hp (yP (fA := fA) p) :=
  Subtype.ext pullback.condition

variable {LA LB p hp}

theorem mP_comp (H : IsHom LA LB p hp) :
    (mP LA p hp).1 ≫ p = pullback.snd p p ≫ fA ≫ unitSec LB := by
  have h1 : pushPt p hp (mP LA p hp) = LB.one _ := by
    rw [mP, H, H.pushPt_inv, pushPt_xP, mul_inv_cancel']
  have h2 := congrArg Subtype.val h1
  rw [pushPt_coe, one_coe] at h2
  simpa only [Category.assoc] using h2

def homPQ (H : IsHom LA LB p hp) : pullback p p ⟶ pullback p (fA ≫ unitSec LB) :=
  pullback.lift (mP LA p hp).1 (pullback.snd p p) (mP_comp H)

@[scoped simp] theorem homPQ_fst (H : IsHom LA LB p hp) :
    homPQ H ≫ pullback.fst _ _ = (mP LA p hp).1 := pullback.lift_fst _ _ _

@[scoped simp] theorem homPQ_snd (H : IsHom LA LB p hp) :
    homPQ H ≫ pullback.snd _ _ = pullback.snd p p := pullback.lift_snd _ _ _

variable (LA LB p hp)

def xQ : SchemeHomOver (pullback.snd p (fA ≫ unitSec LB) ≫ fA) fA :=
  ⟨pullback.fst p (fA ≫ unitSec LB), by
    have h : pullback.fst p (fA ≫ unitSec LB) ≫ p ≫ fB =
        pullback.snd p (fA ≫ unitSec LB) ≫ fA := by
      rw [pullback.condition_assoc, Category.assoc, unitSec_comp, Category.comp_id]
    simpa only [hp] using h⟩

def yQ : SchemeHomOver (pullback.snd p (fA ≫ unitSec LB) ≫ fA) fA :=
  ⟨pullback.snd p (fA ≫ unitSec LB), rfl⟩

def mQ : SchemeHomOver (pullback.snd p (fA ≫ unitSec LB) ≫ fA) fA :=
  LA.mul _ (xQ LB p hp) (yQ LB p)

theorem pushPt_xQ : pushPt p hp (xQ LB p hp) = LB.one _ := by
  apply Subtype.ext
  rw [pushPt_coe, one_coe, xQ, pullback.condition, Category.assoc]

variable {LA LB p hp}

theorem mQ_comp (H : IsHom LA LB p hp) :
    (mQ LA LB p hp).1 ≫ p = pullback.snd p (fA ≫ unitSec LB) ≫ p := by
  have h1 : pushPt p hp (mQ LA LB p hp) = pushPt p hp (yQ LB p) := by
    rw [mQ, H, pushPt_xQ, LB.one_mul]
  exact congrArg Subtype.val h1

def homQP (H : IsHom LA LB p hp) : pullback p (fA ≫ unitSec LB) ⟶ pullback p p :=
  pullback.lift (mQ LA LB p hp).1 (pullback.snd _ _) (mQ_comp H)

@[scoped simp] theorem homQP_fst (H : IsHom LA LB p hp) :
    homQP H ≫ pullback.fst _ _ = (mQ LA LB p hp).1 := pullback.lift_fst _ _ _

@[scoped simp] theorem homQP_snd (H : IsHom LA LB p hp) :
    homQP H ≫ pullback.snd _ _ = pullback.snd _ _ := pullback.lift_snd _ _ _

theorem homPQ_homQP (H : IsHom LA LB p hp) : homPQ H ≫ homQP H = 𝟙 _ := by
  apply pullback.hom_ext
  · rw [Category.assoc, homQP_fst, Category.id_comp]
    have hψ : homPQ H ≫ pullback.snd p (fA ≫ unitSec LB) ≫ fA = pullback.snd p p ≫ fA := by
      rw [← Category.assoc, homPQ_snd]
    have hx : schemeHomOverComp (homPQ H) hψ (xQ LB p hp) = mP LA p hp :=
      Subtype.ext (by rw [schemeHomOverComp_coe, xQ, homPQ_fst])
    have hy : schemeHomOverComp (homPQ H) hψ (yQ LB p) = yP p :=
      Subtype.ext (by rw [schemeHomOverComp_coe, yQ, homPQ_snd, yP])
    have key : schemeHomOverComp (homPQ H) hψ (mQ LA LB p hp) = xP p hp := by
      rw [mQ, LA.mul_natural, hx, hy, mP, inv_mul_cancel_right']
    have := congrArg Subtype.val key
    rw [schemeHomOverComp_coe] at this
    rw [this, xP]
  · rw [Category.assoc, homQP_snd, homPQ_snd, Category.id_comp]

theorem homQP_homPQ (H : IsHom LA LB p hp) : homQP H ≫ homPQ H = 𝟙 _ := by
  apply pullback.hom_ext
  · rw [Category.assoc, homPQ_fst, Category.id_comp]
    have hψ : homQP H ≫ pullback.snd p p ≫ fA = pullback.snd p (fA ≫ unitSec LB) ≫ fA := by
      rw [← Category.assoc, homQP_snd]
    have hx : schemeHomOverComp (homQP H) hψ (xP p hp) = mQ LA LB p hp :=
      Subtype.ext (by rw [schemeHomOverComp_coe, xP, homQP_fst])
    have hy : schemeHomOverComp (homQP H) hψ (yP p) = yQ LB p :=
      Subtype.ext (by rw [schemeHomOverComp_coe, yP, homQP_snd, yQ])
    have key : schemeHomOverComp (homQP H) hψ (mP LA p hp) = xQ LB p hp := by
      rw [mP, LA.mul_natural, inv_natural, hx, hy, mQ, mul_inv_cancel_right']
    have := congrArg Subtype.val key
    rw [schemeHomOverComp_coe] at this
    rw [this, xQ]
  · rw [Category.assoc, homPQ_snd, homQP_snd, Category.id_comp]

scoped instance isIso_homPQ (H : IsHom LA LB p hp) : IsIso (homPQ H) :=
  ⟨⟨homQP H, homPQ_homQP H, homQP_homPQ H⟩⟩

theorem finrank_snd_eq (H : IsHom LA LB p hp) [Flat p] [IsFinite p] :
    (pullback.snd p p).finrank = (pullback.snd p (fA ≫ unitSec LB)).finrank := by
  rw [← homPQ_snd H, Scheme.Hom.finrank_comp_left_of_isIso]

theorem finrank_eq (H : IsHom LA LB p hp) [Flat p] [IsFinite p] [Surjective p] (b : B) :
    p.finrank b = (pullback.snd p (unitSec LB)).finrank (fB.base b) := by
  obtain ⟨a, rfl⟩ := p.surjective b
  have h := congrFun (finrank_snd_eq H) a
  rw [Scheme.Hom.finrank_pullback_snd, Scheme.Hom.finrank_pullback_snd] at h
  rw [Scheme.Hom.finrank_pullback_snd]
  convert h using 2
  change (p ≫ fB ≫ unitSec LB).base a = (fA ≫ unitSec LB).base a
  rw [← Category.assoc, hp]

end WeierstrassProjModel.RelativeGroupLaw.HomFinrankAux
p2m_reactivate "P2MW.S_WeierstrassProjModel_RelativeGroupLaw_finrank_eq_finrank_pullback_snd_one_of_hom.WeierstrassProjModel P2MW.S_WeierstrassProjModel_RelativeGroupLaw_finrank_eq_finrank_pullback_snd_one_of_hom.WeierstrassProjModel.RelativeGroupLaw P2MW.S_WeierstrassProjModel_RelativeGroupLaw_finrank_eq_finrank_pullback_snd_one_of_hom.WeierstrassProjModel.RelativeGroupLaw.HomFinrankAux"
p2m_reactivate "P2MW.S_WeierstrassProjModel_RelativeGroupLaw_finrank_eq_finrank_pullback_snd_one_of_hom.WeierstrassProjModel P2MW.S_WeierstrassProjModel_RelativeGroupLaw_finrank_eq_finrank_pullback_snd_one_of_hom.WeierstrassProjModel.RelativeGroupLaw"
p2m_reactivate "P2MW.S_WeierstrassProjModel_RelativeGroupLaw_finrank_eq_finrank_pullback_snd_one_of_hom.WeierstrassProjModel"

end
p2m_reactivate "P2MW.S_WeierstrassProjModel_RelativeGroupLaw_finrank_eq_finrank_pullback_snd_one_of_hom.WeierstrassProjModel P2MW.S_WeierstrassProjModel_RelativeGroupLaw_finrank_eq_finrank_pullback_snd_one_of_hom.WeierstrassProjModel.RelativeGroupLaw P2MW.S_WeierstrassProjModel_RelativeGroupLaw_finrank_eq_finrank_pullback_snd_one_of_hom.WeierstrassProjModel.RelativeGroupLaw.HomFinrankAux"

theorem solution
    {R : Type} [CommRing R] {A B : Scheme}
    {fA : A ⟶ Spec (CommRingCat.of R)} {fB : B ⟶ Spec (CommRingCat.of R)}
    (LA : RelativeGroupLaw R fA) (LB : RelativeGroupLaw R fB)
    (p : A ⟶ B) (hp : p ≫ fB = fA)
    (p_hom : ∀ {S : Scheme} (t : S ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t fA),
      (⟨(LA.mul t x y).1 ≫ p, by rw [Category.assoc, hp]; exact (LA.mul t x y).2⟩ : SchemeHomOver t fB) =
        LB.mul t ⟨x.1 ≫ p, by rw [Category.assoc, hp]; exact x.2⟩ ⟨y.1 ≫ p, by rw [Category.assoc, hp]; exact y.2⟩)
    [IsFinite p] [Flat p] [LocallyOfFinitePresentation p] [Surjective p] (b : B) :
    p.finrank b = (pullback.snd p (LB.one (𝟙 _)).1).finrank (fB.base b) :=
  WeierstrassProjModel.RelativeGroupLaw.HomFinrankAux.finrank_eq (LA := LA) (LB := LB) (p := p) (hp := hp) (fun t x y => p_hom t x y) b

end S_WeierstrassProjModel_RelativeGroupLaw_finrank_eq_finrank_pullback_snd_one_of_hom
end P2MW
export P2MW.S_WeierstrassProjModel_RelativeGroupLaw_finrank_eq_finrank_pullback_snd_one_of_hom (solution)
