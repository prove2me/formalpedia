-- Prove2me | solution 1 for WeierstrassProjModel.exists_hopfAlgebra_withConv_equiv_torsionSubset_of_isFinite
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/d2694610-2b1b-5c59-bc8d-2adb4898b191

import Definitions.Def_GaloisRep_Flat
import Definitions.Def_WeierstrassCurve_ProjModel
import Theorems.Thm_AlgebraicGeometry_exists_hopfAlgebra_of_grpObj_over_spec
import Theorems.Thm_WeierstrassProjModel_mul_comm_of_isPointsEval
import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassProjModel_exists_hopfAlgebra_withConv_equiv_torsionSubset_of_isFinite
p2m_attr_erase "instance" "WeierstrassProjModel.quotGradingSubmoduleDegreeZeroFiniteType WeierstrassProjModel.kw_lrChart_tensorCommRing WeierstrassProjModel.kw_lrChart_biGrading_gradedAlgebra WeierstrassProjModel.projModel_isIso_spec_mapCR WeierstrassProjModel.kw_lrSymOC_isDomain_ℬ₀ WeierstrassProjModel.isProper_projModelStrCR WeierstrassProjModel.homogeneousSubmoduleDegreeZeroFiniteType"
p2m_attr_erase "simp" "WeierstrassProjModel.kw_lrAdd_substHom_X WeierstrassProjModel.kw_lrSym_substHom_X"

set_option autoImplicit false
set_option Elab.async false

noncomputable section

universe u

p2m_open "AlgebraicGeometry CategoryTheory CategoryTheory.Limits NeronModelInfra WeierstrassProjModel P2MW.S_WeierstrassProjModel_exists_hopfAlgebra_withConv_equiv_torsionSubset_of_isFinite.WeierstrassProjModel"
open scoped CategoryTheory.MonObj

namespace WeierstrassProjModel
p2m_export "WeierstrassProjModel" "schemeHomOverComp schemeHomOverComp_coe RelativeGroupLaw RelativeGroupLaw.pointGroup projModelStrCR galTwist IsPointsEval mul_comm_of_isPointsEval"
p2m_open "WeierstrassProjModel"

namespace RelativeGroupLaw
p2m_export "WeierstrassProjModel.RelativeGroupLaw" "nsmul nsmul_succ pointGroup one_natural nsmul_natural IsTorsionPoint isTorsionPoint_def torsionSubset isTorsionPoint_unit isTorsionPoint_schemeHomOverComp idPoint schemeNsmul schemeNsmul_over schemeKer schemeKerStr mul_one inv_mul_cancel mul_assoc one_mul inv mk mul mul_natural one"
p2m_open "WeierstrassProjModel.RelativeGroupLaw"

variable {R : Type u} [CommRing R]
variable {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)}

theorem d6a_schemeHomOverComp_idPoint {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)}
    (x : SchemeHomOver t f) :
    schemeHomOverComp x.1 x.2 (idPoint (f := f)) = x :=
  Subtype.ext (Category.comp_id x.1)

private theorem _root_.WeierstrassProjModel.RelativeGroupLaw.d6a_nsmul_coe_eq_comp_schemeNsmul (G : RelativeGroupLaw R f) {T : Scheme.{u}}
    {t : T ⟶ Spec (CommRingCat.of R)} (n : ℕ) (x : SchemeHomOver t f) :
    (G.nsmul t n x).1 = x.1 ≫ G.schemeNsmul n := by
  have h : schemeHomOverComp x.1 x.2 (G.nsmul f n idPoint)
      = G.nsmul t n (schemeHomOverComp x.1 x.2 idPoint) :=
    G.nsmul_natural f t x.1 x.2 n idPoint
  rw [d6a_schemeHomOverComp_idPoint] at h
  exact (congrArg Subtype.val h).symm

p2m_export "WeierstrassProjModel.RelativeGroupLaw" "d6a_nsmul_coe_eq_comp_schemeNsmul"

private theorem _root_.WeierstrassProjModel.RelativeGroupLaw.d6a_one_coe_eq_comp_one (G : RelativeGroupLaw R f) {T : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of R)) :
    (G.one t).1 = t ≫ (G.one (𝟙 (Spec (CommRingCat.of R)))).1 := by
  have h : schemeHomOverComp t (Category.comp_id t) (G.one (𝟙 _)) = G.one t :=
    G.one_natural (𝟙 _) t t (Category.comp_id t)
  exact (congrArg Subtype.val h).symm

p2m_export "WeierstrassProjModel.RelativeGroupLaw" "d6a_one_coe_eq_comp_one"
open CategoryTheory.Limits

private theorem _root_.WeierstrassProjModel.RelativeGroupLaw.d6a_schemeKer_fst_comp_f (G : RelativeGroupLaw R f) (n : ℕ) :
    (pullback.fst (G.schemeNsmul n) (G.one (𝟙 _)).1 ≫ f
        : G.schemeKer n ⟶ Spec (CommRingCat.of R))
      = pullback.snd (G.schemeNsmul n) (G.one (𝟙 _)).1 := by
  have h := congrArg (· ≫ f)
    (pullback.condition (f := G.schemeNsmul n) (g := (G.one (𝟙 _)).1))
  simp only [Category.assoc, G.schemeNsmul_over n, (G.one (𝟙 _)).2, Category.comp_id] at h
  exact h

p2m_export "WeierstrassProjModel.RelativeGroupLaw" "d6a_schemeKer_fst_comp_f"

private def _root_.WeierstrassProjModel.RelativeGroupLaw.d6a_torsionSubsetEquivKerPoints (G : RelativeGroupLaw R f) {T : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of R)) (n : ℕ) :
    G.torsionSubset t n ≃
      SchemeHomOver t (pullback.snd (G.schemeNsmul n) (G.one (𝟙 _)).1) where
  toFun x :=
    ⟨pullback.lift x.1.1 t
        (by
          have hx : (G.nsmul t n x.1).1 = (G.one t).1 := congrArg Subtype.val x.2
          rw [G.d6a_nsmul_coe_eq_comp_schemeNsmul, G.d6a_one_coe_eq_comp_one] at hx
          exact hx),
      pullback.lift_snd _ _ _⟩
  invFun ψ :=
    ⟨⟨ψ.1 ≫ pullback.fst _ _, by rw [Category.assoc, G.d6a_schemeKer_fst_comp_f, ψ.2]⟩,
      show G.nsmul t n _ = G.one t from Subtype.ext (by
        have hcond := congrArg (ψ.1 ≫ ·)
          (pullback.condition (f := G.schemeNsmul n) (g := (G.one (𝟙 _)).1))
        simp only [← Category.assoc, ψ.2] at hcond
        rw [G.d6a_nsmul_coe_eq_comp_schemeNsmul]
        exact hcond.trans (G.d6a_one_coe_eq_comp_one t).symm)⟩
  left_inv x := Subtype.ext (Subtype.ext (pullback.lift_fst _ _ _))
  right_inv ψ := Subtype.ext
    (pullback.hom_ext (by rw [pullback.lift_fst]) (by rw [pullback.lift_snd, ψ.2]))

p2m_export "WeierstrassProjModel.RelativeGroupLaw" "d6a_torsionSubsetEquivKerPoints"
end RelativeGroupLaw

end WeierstrassProjModel

namespace WeierstrassProjModel
p2m_export "WeierstrassProjModel" "schemeHomOverComp schemeHomOverComp_coe RelativeGroupLaw RelativeGroupLaw.pointGroup projModelStrCR galTwist IsPointsEval mul_comm_of_isPointsEval"
p2m_open "WeierstrassProjModel"

open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory

variable {R : Type u} [CommRing R] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)}

section GeneralDictionary

def d6a_overHomEquivSchemeHomOver (T : Over (Spec (CommRingCat.of R)))
    (f : A ⟶ Spec (CommRingCat.of R)) :
    (T ⟶ Over.mk f) ≃ SchemeHomOver T.hom f where
  toFun φ := ⟨φ.left, by simpa using Over.w φ⟩
  invFun x := Over.homMk x.1 (by simpa using x.2)
  left_inv φ := Over.OverMorphism.ext (by simp)
  right_inv x := Subtype.ext (by simp)

@[scoped simp]
theorem d6a_overHomEquivSchemeHomOver_apply_coe (T : Over (Spec (CommRingCat.of R)))
    (f : A ⟶ Spec (CommRingCat.of R)) (φ : T ⟶ Over.mk f) :
    (d6a_overHomEquivSchemeHomOver T f φ).1 = φ.left :=
  rfl

@[scoped simp]
theorem d6a_overHomEquivSchemeHomOver_symm_apply_left (T : Over (Spec (CommRingCat.of R)))
    (f : A ⟶ Spec (CommRingCat.of R)) (x : SchemeHomOver T.hom f) :
    ((d6a_overHomEquivSchemeHomOver T f).symm x).left = x.1 :=
  rfl

end GeneralDictionary

section DirectionTwo

namespace RelativeGroupLaw p2m_export "WeierstrassProjModel.RelativeGroupLaw" "nsmul nsmul_succ pointGroup one_natural nsmul_natural IsTorsionPoint isTorsionPoint_def torsionSubset isTorsionPoint_unit isTorsionPoint_schemeHomOverComp idPoint schemeNsmul schemeNsmul_over schemeKer schemeKerStr mul_one inv_mul_cancel mul_assoc one_mul inv mk mul mul_natural one" end RelativeGroupLaw
namespace RelativeGroupLaw
p2m_open_scoped "WeierstrassProjModel.RelativeGroupLaw" in

private def _root_.WeierstrassProjModel.RelativeGroupLaw.d6a_yonedaGrpObjPresheaf (G : RelativeGroupLaw R f) :
    (Over (Spec (CommRingCat.of R)))ᵒᵖ ⥤ GrpCat.{u} where
  obj T := @GrpCat.of (SchemeHomOver T.unop.hom f) (G.pointGroup T.unop.hom)
  map {S T} χ :=
    letI := G.pointGroup S.unop.hom
    letI := G.pointGroup T.unop.hom
    GrpCat.ofHom
      { toFun := fun x => schemeHomOverComp χ.unop.left (Over.w χ.unop) x
        map_one' := G.one_natural _ _ _ _
        map_mul' := fun x y => G.mul_natural _ _ _ _ x y }
  map_id S := by
    letI := G.pointGroup S.unop.hom
    refine GrpCat.hom_ext (MonoidHom.ext fun x => Subtype.ext ?_)
    simp
  map_comp {S T U} χ χ' := by
    letI := G.pointGroup S.unop.hom
    letI := G.pointGroup T.unop.hom
    letI := G.pointGroup U.unop.hom
    refine GrpCat.hom_ext (MonoidHom.ext fun x => Subtype.ext ?_)
    simp

end RelativeGroupLaw
p2m_export "WeierstrassProjModel" "RelativeGroupLaw.d6a_yonedaGrpObjPresheaf"
namespace RelativeGroupLaw
p2m_open_scoped "WeierstrassProjModel.RelativeGroupLaw" in

private def _root_.WeierstrassProjModel.RelativeGroupLaw.d6a_overMkRepresentableBy (G : RelativeGroupLaw R f) :
    (G.d6a_yonedaGrpObjPresheaf ⋙ forget GrpCat).RepresentableBy (Over.mk f) where
  homEquiv {T} := d6a_overHomEquivSchemeHomOver T f
  homEquiv_comp _ _ := Subtype.ext rfl

end RelativeGroupLaw
p2m_export "WeierstrassProjModel" "RelativeGroupLaw.d6a_overMkRepresentableBy"
namespace RelativeGroupLaw
p2m_open_scoped "WeierstrassProjModel.RelativeGroupLaw" in

@[reducible]
private def _root_.WeierstrassProjModel.RelativeGroupLaw.d6a_grpObjOverMk (G : RelativeGroupLaw R f) : GrpObj (Over.mk f) :=
  GrpObj.ofRepresentableBy (Over.mk f) G.d6a_yonedaGrpObjPresheaf G.d6a_overMkRepresentableBy

end RelativeGroupLaw
p2m_export "WeierstrassProjModel" "RelativeGroupLaw.d6a_grpObjOverMk"
end DirectionTwo

section SeamEquations

variable (G : RelativeGroupLaw R f)

namespace RelativeGroupLaw
p2m_open_scoped "WeierstrassProjModel.RelativeGroupLaw" in

private theorem _root_.WeierstrassProjModel.RelativeGroupLaw.d6a_overHomEquivSchemeHomOver_mul (T : Over (Spec (CommRingCat.of R)))
    (a b : T ⟶ Over.mk f) :
    letI := G.d6a_grpObjOverMk
    d6a_overHomEquivSchemeHomOver T f (a * b) =
      G.mul T.hom (d6a_overHomEquivSchemeHomOver T f a) (d6a_overHomEquivSchemeHomOver T f b) := by
  letI := G.d6a_grpObjOverMk
  exact ((yonedaGrpObjIsoOfRepresentableBy (Over.mk f) G.d6a_yonedaGrpObjPresheaf
    G.d6a_overMkRepresentableBy).hom.app (Opposite.op T)).hom.map_mul a b

end RelativeGroupLaw
p2m_export "WeierstrassProjModel" "RelativeGroupLaw.d6a_overHomEquivSchemeHomOver_mul"
end SeamEquations

end WeierstrassProjModel
p2m_reactivate "P2MW.S_WeierstrassProjModel_exists_hopfAlgebra_withConv_equiv_torsionSubset_of_isFinite.WeierstrassProjModel"

namespace WeierstrassProjModel
p2m_export "WeierstrassProjModel" "schemeHomOverComp schemeHomOverComp_coe RelativeGroupLaw RelativeGroupLaw.pointGroup projModelStrCR galTwist IsPointsEval mul_comm_of_isPointsEval"
p2m_open "WeierstrassProjModel"

namespace RelativeGroupLaw
p2m_export "WeierstrassProjModel.RelativeGroupLaw" "nsmul nsmul_succ pointGroup one_natural nsmul_natural IsTorsionPoint isTorsionPoint_def torsionSubset isTorsionPoint_unit isTorsionPoint_schemeHomOverComp idPoint schemeNsmul schemeNsmul_over schemeKer schemeKerStr mul_one inv_mul_cancel mul_assoc one_mul inv mk mul mul_natural one"
p2m_open "WeierstrassProjModel.RelativeGroupLaw"

variable {R : Type u} [CommRing R]
variable {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)}

section TorsionStability

variable (G : RelativeGroupLaw R f)

private theorem _root_.WeierstrassProjModel.RelativeGroupLaw.d6a_nsmul_eq_pow {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
    (n : ℕ) (x : SchemeHomOver t f) :
    letI := G.pointGroup t
    G.nsmul t n x = x ^ n := by
  letI := G.pointGroup t
  induction n with
  | zero => rfl
  | succ n ih => rw [nsmul_succ, ih, pow_succ]; rfl

p2m_export "WeierstrassProjModel.RelativeGroupLaw" "d6a_nsmul_eq_pow"

private theorem _root_.WeierstrassProjModel.RelativeGroupLaw.d6a_nsmul_inv {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
    (n : ℕ) (x : SchemeHomOver t f) :
    G.nsmul t n (G.inv t x) = G.inv t (G.nsmul t n x) := by
  letI := G.pointGroup t
  rw [G.d6a_nsmul_eq_pow, G.d6a_nsmul_eq_pow]
  exact inv_pow x n

p2m_export "WeierstrassProjModel.RelativeGroupLaw" "d6a_nsmul_inv"

private theorem _root_.WeierstrassProjModel.RelativeGroupLaw.d6a_isTorsionPoint_inv {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
    (n : ℕ) {x : SchemeHomOver t f} (hx : G.IsTorsionPoint t n x) :
    G.IsTorsionPoint t n (G.inv t x) := by
  letI := G.pointGroup t
  rw [isTorsionPoint_def, G.d6a_nsmul_inv, hx]
  exact inv_one

p2m_export "WeierstrassProjModel.RelativeGroupLaw" "d6a_isTorsionPoint_inv"
variable (hcomm : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
  (x y : SchemeHomOver t f), G.mul t x y = G.mul t y x)

include hcomm in

private theorem _root_.WeierstrassProjModel.RelativeGroupLaw.d6a_nsmul_mul {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
    (n : ℕ) (x y : SchemeHomOver t f) :
    G.nsmul t n (G.mul t x y) = G.mul t (G.nsmul t n x) (G.nsmul t n y) := by
  induction n with
  | zero => simp [G.one_mul]
  | succ n ih =>
      rw [nsmul_succ, ih, nsmul_succ, nsmul_succ, G.mul_assoc, G.mul_assoc]
      congr 1
      rw [← G.mul_assoc, hcomm t (G.nsmul t n y) x, G.mul_assoc]

p2m_export "WeierstrassProjModel.RelativeGroupLaw" "d6a_nsmul_mul"
include hcomm in

private theorem _root_.WeierstrassProjModel.RelativeGroupLaw.d6a_isTorsionPoint_mul {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
    (n : ℕ) {x y : SchemeHomOver t f} (hx : G.IsTorsionPoint t n x)
    (hy : G.IsTorsionPoint t n y) :
    G.IsTorsionPoint t n (G.mul t x y) := by
  rw [isTorsionPoint_def, G.d6a_nsmul_mul hcomm t n x y, hx, hy, G.one_mul]

p2m_export "WeierstrassProjModel.RelativeGroupLaw" "d6a_isTorsionPoint_mul"
end TorsionStability
p2m_reactivate "P2MW.S_WeierstrassProjModel_exists_hopfAlgebra_withConv_equiv_torsionSubset_of_isFinite.WeierstrassProjModel"

section KernelLaw

variable (G : RelativeGroupLaw R f) (n : ℕ)

private abbrev _root_.WeierstrassProjModel.RelativeGroupLaw.d6a_kerIncl {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)}
    (φ : SchemeHomOver t (G.schemeKerStr n)) : SchemeHomOver t f :=
  ((G.d6a_torsionSubsetEquivKerPoints t n).symm φ).1

p2m_export "WeierstrassProjModel.RelativeGroupLaw" "d6a_kerIncl"

private theorem _root_.WeierstrassProjModel.RelativeGroupLaw.d6a_isTorsionPoint_kerIncl {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)}
    (φ : SchemeHomOver t (G.schemeKerStr n)) :
    G.IsTorsionPoint t n (G.d6a_kerIncl n φ) :=
  ((G.d6a_torsionSubsetEquivKerPoints t n).symm φ).2

p2m_export "WeierstrassProjModel.RelativeGroupLaw" "d6a_isTorsionPoint_kerIncl"

@[scoped simp]
private theorem _root_.WeierstrassProjModel.RelativeGroupLaw.d6a_kerIncl_equiv {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)}
    (x : G.torsionSubset t n) :
    G.d6a_kerIncl n (G.d6a_torsionSubsetEquivKerPoints t n x) = x.1 :=
  congrArg Subtype.val ((G.d6a_torsionSubsetEquivKerPoints t n).symm_apply_apply x)

p2m_export "WeierstrassProjModel.RelativeGroupLaw" "d6a_kerIncl_equiv"

private theorem _root_.WeierstrassProjModel.RelativeGroupLaw.d6a_kerIncl_schemeHomOverComp {T T' : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
    (t' : T' ⟶ Spec (CommRingCat.of R)) (ψ : T' ⟶ T) (hψ : ψ ≫ t = t')
    (φ : SchemeHomOver t (G.schemeKerStr n)) :
    G.d6a_kerIncl n (schemeHomOverComp ψ hψ φ) = schemeHomOverComp ψ hψ (G.d6a_kerIncl n φ) :=
  Subtype.ext (Category.assoc ψ φ.1 _).symm

p2m_export "WeierstrassProjModel.RelativeGroupLaw" "d6a_kerIncl_schemeHomOverComp"

private theorem _root_.WeierstrassProjModel.RelativeGroupLaw.d6a_schemeHomOverComp_torsionSubsetEquivKerPoints {T T' : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of R)) (t' : T' ⟶ Spec (CommRingCat.of R))
    (ψ : T' ⟶ T) (hψ : ψ ≫ t = t') (x : G.torsionSubset t n) :
    schemeHomOverComp ψ hψ (G.d6a_torsionSubsetEquivKerPoints t n x) =
      G.d6a_torsionSubsetEquivKerPoints t' n
        ⟨schemeHomOverComp ψ hψ x.1, G.isTorsionPoint_schemeHomOverComp t t' ψ hψ n x.2⟩ := by
  refine Subtype.ext (pullback.hom_ext ?_ ?_)
  · simp only [schemeHomOverComp_coe, d6a_torsionSubsetEquivKerPoints, Equiv.coe_fn_mk,
      Category.assoc, pullback.lift_fst]
  · simp only [schemeHomOverComp_coe, d6a_torsionSubsetEquivKerPoints, Equiv.coe_fn_mk,
      Category.assoc, pullback.lift_snd, hψ]

p2m_export "WeierstrassProjModel.RelativeGroupLaw" "d6a_schemeHomOverComp_torsionSubsetEquivKerPoints"
variable (hcomm : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
  (x y : SchemeHomOver t f), G.mul t x y = G.mul t y x)

include hcomm in

private def _root_.WeierstrassProjModel.RelativeGroupLaw.d6a_kerLaw : RelativeGroupLaw R (G.schemeKerStr n) where
  mul {T} t φ ψ := G.d6a_torsionSubsetEquivKerPoints t n
    ⟨G.mul t (G.d6a_kerIncl n φ) (G.d6a_kerIncl n ψ),
      G.d6a_isTorsionPoint_mul hcomm t n (G.d6a_isTorsionPoint_kerIncl n φ)
        (G.d6a_isTorsionPoint_kerIncl n ψ)⟩
  one {T} t := G.d6a_torsionSubsetEquivKerPoints t n ⟨G.one t, G.isTorsionPoint_unit t n⟩
  inv {T} t φ := G.d6a_torsionSubsetEquivKerPoints t n
    ⟨G.inv t (G.d6a_kerIncl n φ), G.d6a_isTorsionPoint_inv t n (G.d6a_isTorsionPoint_kerIncl n φ)⟩
  mul_assoc {T} t φ ψ χ := by
    refine congrArg _ (Subtype.ext ?_)
    simp only [d6a_kerIncl_equiv]
    exact G.mul_assoc t _ _ _
  one_mul {T} t φ := by
    conv_rhs => rw [← (G.d6a_torsionSubsetEquivKerPoints t n).apply_symm_apply φ]
    refine congrArg _ (Subtype.ext ?_)
    simp only [d6a_kerIncl_equiv]
    exact G.one_mul t _
  mul_one {T} t φ := by
    conv_rhs => rw [← (G.d6a_torsionSubsetEquivKerPoints t n).apply_symm_apply φ]
    refine congrArg _ (Subtype.ext ?_)
    simp only [d6a_kerIncl_equiv]
    exact G.mul_one t _
  inv_mul_cancel {T} t φ := by
    refine congrArg _ (Subtype.ext ?_)
    simp only [d6a_kerIncl_equiv]
    exact G.inv_mul_cancel t _
  mul_natural {T T'} t t' ψ hψ φ χ := by
    rw [show schemeHomOverComp ψ hψ (G.d6a_torsionSubsetEquivKerPoints t n _)
      = G.d6a_torsionSubsetEquivKerPoints t' n _
      from G.d6a_schemeHomOverComp_torsionSubsetEquivKerPoints n t t' ψ hψ _]
    refine congrArg _ (Subtype.ext ?_)
    simp only [G.d6a_kerIncl_schemeHomOverComp n t t' ψ hψ]
    exact G.mul_natural t t' ψ hψ _ _

p2m_export "WeierstrassProjModel.RelativeGroupLaw" "d6a_kerLaw"
include hcomm in

@[scoped simp]
private theorem _root_.WeierstrassProjModel.RelativeGroupLaw.d6a_kerIncl_kerLaw_mul {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
    (φ ψ : SchemeHomOver t (G.schemeKerStr n)) :
    G.d6a_kerIncl n ((G.d6a_kerLaw n hcomm).mul t φ ψ) = G.mul t (G.d6a_kerIncl n φ) (G.d6a_kerIncl n ψ) :=
  G.d6a_kerIncl_equiv n _

p2m_export "WeierstrassProjModel.RelativeGroupLaw" "d6a_kerIncl_kerLaw_mul"
include hcomm in

@[scoped simp]
theorem d6a_kerIncl_kerLaw_one {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) :
    G.d6a_kerIncl n ((G.d6a_kerLaw n hcomm).one t) = G.one t :=
  G.d6a_kerIncl_equiv n _

include hcomm in

private theorem _root_.WeierstrassProjModel.RelativeGroupLaw.d6a_kerLaw_mul_comm {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
    (φ ψ : SchemeHomOver t (G.schemeKerStr n)) :
    (G.d6a_kerLaw n hcomm).mul t φ ψ = (G.d6a_kerLaw n hcomm).mul t ψ φ := by
  show G.d6a_torsionSubsetEquivKerPoints t n _ = G.d6a_torsionSubsetEquivKerPoints t n _
  exact congrArg _ (Subtype.ext (hcomm t _ _))

p2m_export "WeierstrassProjModel.RelativeGroupLaw" "d6a_kerLaw_mul_comm"
end KernelLaw
p2m_reactivate "P2MW.S_WeierstrassProjModel_exists_hopfAlgebra_withConv_equiv_torsionSubset_of_isFinite.WeierstrassProjModel"

section DockInstances

variable (G : RelativeGroupLaw R f) (n : ℕ)
variable (hcomm : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
  (x y : SchemeHomOver t f), G.mul t x y = G.mul t y x)

open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory

include hcomm in

@[reducible]
private def _root_.WeierstrassProjModel.RelativeGroupLaw.d6a_grpObjSchemeKer : GrpObj (Over.mk (G.schemeKerStr n)) :=
  (G.d6a_kerLaw n hcomm).d6a_grpObjOverMk

p2m_export "WeierstrassProjModel.RelativeGroupLaw" "d6a_grpObjSchemeKer"
include hcomm in

private theorem _root_.WeierstrassProjModel.RelativeGroupLaw.d6a_isCommMonObj_schemeKer :
    letI := G.d6a_grpObjSchemeKer n hcomm
    IsCommMonObj (Over.mk (G.schemeKerStr n)) := by
  letI := G.d6a_grpObjSchemeKer n hcomm
  rw [isCommMonObj_iff_isMulCommutative]
  intro X
  constructor
  constructor
  intro a b
  apply (d6a_overHomEquivSchemeHomOver X (G.schemeKerStr n)).injective
  rw [(G.d6a_kerLaw n hcomm).d6a_overHomEquivSchemeHomOver_mul X a b,
    (G.d6a_kerLaw n hcomm).d6a_overHomEquivSchemeHomOver_mul X b a]
  exact G.d6a_kerLaw_mul_comm n hcomm X.hom _ _

p2m_export "WeierstrassProjModel.RelativeGroupLaw" "d6a_isCommMonObj_schemeKer"
include hcomm in

private theorem _root_.WeierstrassProjModel.RelativeGroupLaw.d6a_kerIncl_overHomMul_eq_mul (T : Over (Spec (CommRingCat.of R)))
    (a b : T ⟶ Over.mk (G.schemeKerStr n)) :
    letI := G.d6a_grpObjSchemeKer n hcomm
    G.d6a_kerIncl n (d6a_overHomEquivSchemeHomOver T (G.schemeKerStr n) (a * b))
      = G.mul T.hom (G.d6a_kerIncl n (d6a_overHomEquivSchemeHomOver T (G.schemeKerStr n) a))
          (G.d6a_kerIncl n (d6a_overHomEquivSchemeHomOver T (G.schemeKerStr n) b)) := by
  letI := G.d6a_grpObjSchemeKer n hcomm
  rw [(G.d6a_kerLaw n hcomm).d6a_overHomEquivSchemeHomOver_mul T a b]
  exact G.d6a_kerIncl_kerLaw_mul n hcomm T.hom _ _

p2m_export "WeierstrassProjModel.RelativeGroupLaw" "d6a_kerIncl_overHomMul_eq_mul"
end DockInstances
p2m_reactivate "P2MW.S_WeierstrassProjModel_exists_hopfAlgebra_withConv_equiv_torsionSubset_of_isFinite.WeierstrassProjModel"

end RelativeGroupLaw
p2m_reactivate "P2MW.S_WeierstrassProjModel_exists_hopfAlgebra_withConv_equiv_torsionSubset_of_isFinite.WeierstrassProjModel P2MW.S_WeierstrassProjModel_exists_hopfAlgebra_withConv_equiv_torsionSubset_of_isFinite.WeierstrassProjModel.RelativeGroupLaw"

end WeierstrassProjModel
p2m_reactivate "P2MW.S_WeierstrassProjModel_exists_hopfAlgebra_withConv_equiv_torsionSubset_of_isFinite.WeierstrassProjModel P2MW.S_WeierstrassProjModel_exists_hopfAlgebra_withConv_equiv_torsionSubset_of_isFinite.WeierstrassProjModel.RelativeGroupLaw"

open scoped WeierstrassCurve.Affine in
open WeierstrassCurve WeierstrassCurve.Affine.Point in

theorem solution
    (K : Type) [Field K] (W : WeierstrassCurve K) [W.IsElliptic] (n : ℕ)
    (G : RelativeGroupLaw K (projModelStrCR W.toProjective))
    (ev : ∀ (F : Type) [Field F] [DecidableEq F] [Algebra K F],
      SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap K F)))
          (projModelStrCR W.toProjective) ≃
        (W.toProjective.baseChange F).toAffine.Point)
    (hev : IsPointsEval W.toProjective G ev)
    (hfin : IsFinite (G.schemeKerStr n)) :
    letI : DecidableEq (AlgebraicClosure K) := Classical.decEq _
    ∃ (A : Type) (_ : CommRing A) (_ : HopfAlgebra K A),
      Module.Finite K A ∧ Coalgebra.IsCocomm K A ∧
      ∃ eH : WithConv (A →ₐ[K] AlgebraicClosure K) ≃
            ↥(G.torsionSubset (Spec.map (CommRingCat.ofHom
              (algebraMap K (AlgebraicClosure K)))) n),
        (∀ f g, (eH (f * g)).1 =
          G.mul (Spec.map (CommRingCat.ofHom (algebraMap K (AlgebraicClosure K))))
            (eH f).1 (eH g).1) ∧
        ∀ (σ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K)
          (f g : WithConv (A →ₐ[K] AlgebraicClosure K)),
          (∀ a : A, g a = σ (f a)) → (eH g).1 = galTwist σ (eH f).1 := by
  have hcomm : ∀ {T : Scheme} (t : T ⟶ Spec (CommRingCat.of K))
      (x y : SchemeHomOver t (projModelStrCR W.toProjective)),
      G.mul t x y = G.mul t y x := fun t x y => WeierstrassProjModel.mul_comm_of_isPointsEval K W G ev hev t x y
  letI instGrp := G.d6a_grpObjSchemeKer n hcomm
  haveI := G.d6a_isCommMonObj_schemeKer n hcomm
  haveI : IsFinite (Over.mk (G.schemeKerStr n)).hom := hfin
  obtain ⟨A, iCR, iHopf, hA, hco, e, hmul, hnat⟩ :=
    AlgebraicGeometry.exists_hopfAlgebra_of_grpObj_over_spec K (Over.mk (G.schemeKerStr n))
  letI := iCR
  letI := iHopf
  refine ⟨A, iCR, iHopf, hA, hco,
    (e (AlgebraicClosure K)).trans
      ((d6a_overHomEquivSchemeHomOver (Over.mk (Spec.map (CommRingCat.ofHom
            (algebraMap K (AlgebraicClosure K))))) (G.schemeKerStr n)).trans
        (G.d6a_torsionSubsetEquivKerPoints (Spec.map (CommRingCat.ofHom
            (algebraMap K (AlgebraicClosure K)))) n).symm), ?_, ?_⟩
  ·
    intro φ ψ
    have h1 := hmul (AlgebraicClosure K) φ ψ
    show G.d6a_kerIncl n (d6a_overHomEquivSchemeHomOver _ _ (e (AlgebraicClosure K) (φ * ψ))) = _
    rw [h1]
    exact G.d6a_kerIncl_overHomMul_eq_mul n hcomm _ _ _
  ·
    intro σ φ ψ hσ
    have hψ : ψ = WithConv.toConv
        (((σ : AlgebraicClosure K →ₐ[K] AlgebraicClosure K)).comp (WithConv.ofConv φ)) := by
      refine WithConv.ext ?_
      exact AlgHom.ext fun a => hσ a
    have hleft : (e (AlgebraicClosure K) ψ).left
        = Spec.map (CommRingCat.ofHom
            ((σ : AlgebraicClosure K →ₐ[K] AlgebraicClosure K)).toRingHom)
          ≫ (e (AlgebraicClosure K) φ).left := by
      rw [hψ]
      exact hnat _ _ ((σ : AlgebraicClosure K →ₐ[K] AlgebraicClosure K)) φ
    have hcoe : ((σ : AlgebraicClosure K →ₐ[K] AlgebraicClosure K)).toRingHom
        = ((σ : AlgebraicClosure K →+* AlgebraicClosure K)) := rfl
    show G.d6a_kerIncl n (d6a_overHomEquivSchemeHomOver _ _ (e (AlgebraicClosure K) ψ))
        = galTwist σ (G.d6a_kerIncl n (d6a_overHomEquivSchemeHomOver _ _ (e (AlgebraicClosure K) φ)))
    refine Subtype.ext ?_
    show (e (AlgebraicClosure K) ψ).left
          ≫ pullback.fst (G.schemeNsmul n) (G.one (𝟙 (Spec (CommRingCat.of K)))).1
        = Spec.map (CommRingCat.ofHom ((σ : AlgebraicClosure K →+* AlgebraicClosure K)))
          ≫ ((e (AlgebraicClosure K) φ).left
              ≫ pullback.fst (G.schemeNsmul n) (G.one (𝟙 (Spec (CommRingCat.of K)))).1)
    rw [hleft, hcoe]
    exact Category.assoc _ _ _

end
p2m_reactivate "P2MW.S_WeierstrassProjModel_exists_hopfAlgebra_withConv_equiv_torsionSubset_of_isFinite.WeierstrassProjModel P2MW.S_WeierstrassProjModel_exists_hopfAlgebra_withConv_equiv_torsionSubset_of_isFinite.WeierstrassProjModel.RelativeGroupLaw"

end S_WeierstrassProjModel_exists_hopfAlgebra_withConv_equiv_torsionSubset_of_isFinite
end P2MW
export P2MW.S_WeierstrassProjModel_exists_hopfAlgebra_withConv_equiv_torsionSubset_of_isFinite (solution)
