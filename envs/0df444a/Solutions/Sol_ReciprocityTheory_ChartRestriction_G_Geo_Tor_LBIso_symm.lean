-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Geo.Tor.LBIso.symm
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:35:18.63282+00:00
-- url     : https://prove2.me/submissions/303f535e-7a12-41db-b469-3bd7a94505f4

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Splits
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_OLinBaseChangeSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_BCTools
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
namespace ReciprocityTheory.ChartRestriction.G.Geo.Tor
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Semi
open scoped CategoryTheory.Obj
section Grp
variable {S S' : Scheme.{0}}
end Grp
section Iso
variable {X Y Y' : Scheme.{0}}
private lemma res_res_toroidal_compactification {A : Scheme.{0}} {U V W : A.Opens} (h1 : W ≤ V) (h2 : V ≤ U) (u : Γ(A, U)ˣ) :
    res h1 (res h2 u) = res (h1.trans h2) u := by
  ext1
  have e := congrArg (fun g => g.hom (u : Γ(A, U))) (A.presheaf.map_comp (homOfLE h2).op (homOfLE h1).op)
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at e
  simp only [res, Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe]
  exact e.symm
private lemma res_mul_inv_mul_of_eq {A : Scheme.{0}} {U V : A.Opens} (h : V ≤ U) (x y z w : Γ(A, U)ˣ)
    (hx : x = y * z⁻¹ * w) : res h x = res h y * (res h z)⁻¹ * res h w := by
  rw [hx, map_mul, map_mul, map_inv]
private lemma inv_eq_mul_inv_mul_inv_of_eq_mul_inv_mul {G : Type*} [CommGroup G] (x a b y : G) (h : x = a * b⁻¹ * y) :
    x⁻¹ = b * a⁻¹ * y⁻¹ := by
  rw [h]
  simp only [mul_inv_rev, inv_inv]
  exact mul_comm _ _
end Iso
section Field
variable {F : Type} [Field F] {X : Scheme.{0}}
variable {B B' B₀ : Scheme.{0}} {M : LB B} {M' : LB B'} {M₀ : LB B₀} {K : Type} [Fintype K] {ε : K → ℤ}
end Field
end ReciprocityTheory.ChartRestriction.G.Geo.Tor
end
end

set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Semi
open scoped CategoryTheory.Obj
variable {X Y Y' : Scheme.{0}}
namespace ReciprocityTheory.ChartRestriction.G.Geo.Tor
namespace LBIso
theorem _root_.solution {A B : LB X} (H : LBIso A B) : LBIso B A := by
  obtain ⟨w, hw⟩ := H
  refine ⟨⟨fun p => (res (le_inf inf_le_right inf_le_left : A.U p.1 ⊓ B.U p.2 ≤ B.U p.2 ⊓ A.U p.1)
    (w.s (p.2, p.1)))⁻¹⟩, fun p q => ?_⟩
  have hc : (A.U p.1 ⊓ B.U p.2 ⊓ (A.U q.1 ⊓ B.U q.2)) ≤ B.U p.2 ⊓ A.U p.1 ⊓ (B.U q.2 ⊓ A.U q.1) :=
    le_inf (le_inf (inf_le_left.trans inf_le_right) (inf_le_left.trans inf_le_left))
      (le_inf (inf_le_right.trans inf_le_right) (inf_le_right.trans inf_le_left))
  have hg := hw (p.2, p.1) (q.2, q.1)
  have e := res_mul_inv_mul_of_eq hc _ _ _ _ hg
  have e2 := inv_eq_mul_inv_mul_inv_of_eq_mul_inv_mul _ _ _ _ e
  show res (inf_le_left : (A.U p.1 ⊓ B.U p.2 ⊓ (A.U q.1 ⊓ B.U q.2)) ≤ A.U p.1 ⊓ B.U p.2)
      (res (le_inf inf_le_right inf_le_left : A.U p.1 ⊓ B.U p.2 ≤ B.U p.2 ⊓ A.U p.1) (w.s (p.2, p.1)))⁻¹ =
    res (le_inf (inf_le_left.trans inf_le_left) (inf_le_right.trans inf_le_left) : (A.U p.1 ⊓ B.U p.2 ⊓ (A.U q.1 ⊓ B.U q.2)) ≤ A.U p.1 ⊓ A.U q.1)
        (A.g p.1 q.1) *
      (res (le_inf (inf_le_left.trans inf_le_right) (inf_le_right.trans inf_le_right) : (A.U p.1 ⊓ B.U p.2 ⊓ (A.U q.1 ⊓ B.U q.2)) ≤ B.U p.2 ⊓ B.U q.2)
        (B.g p.2 q.2))⁻¹ *
      res (inf_le_right : (A.U p.1 ⊓ B.U p.2 ⊓ (A.U q.1 ⊓ B.U q.2)) ≤ A.U q.1 ⊓ B.U q.2)
        (res (le_inf inf_le_right inf_le_left : A.U q.1 ⊓ B.U q.2 ≤ B.U q.2 ⊓ A.U q.1) (w.s (q.2, q.1)))⁻¹
  rw [map_inv, map_inv]
  refine (congrArg Inv.inv ((res_res_toroidal_compactification _ _ _).trans (res_res_toroidal_compactification _ _ _).symm)).trans (e2.trans ?_)
  refine congrArg₂ (· * ·) (congrArg₂ (· * ·) (res_res_toroidal_compactification _ _ _) (congrArg Inv.inv (res_res_toroidal_compactification _ _ _))) ?_
  exact congrArg Inv.inv ((res_res_toroidal_compactification _ _ _).trans (res_res_toroidal_compactification _ _ _).symm)
end LBIso
end ReciprocityTheory.ChartRestriction.G.Geo.Tor
