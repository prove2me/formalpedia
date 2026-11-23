-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Geo.Tor.exists_div_sec
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:30:17.334969+00:00
-- url     : https://prove2.me/submissions/585e9483-b105-4d3b-ad26-dc4531e80c08

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsLieBasis
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DivCalc
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gs_constFn
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_cst_regular
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_exists_div
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
open AlgebraicGeometry CategoryTheory Limits TopologicalSpace Opposite TensorProduct
open ReciprocityTheory.ChartRestriction.G.Semi
variable {V : Type} [CommRing V] {X Z : Scheme.{0}}
private theorem presheaf_map_constFn' (p : X ⟶ Sp V) {A B : X.Opens} (i : B ⟶ A) (a : V) :
    (X.presheaf.map i.op).hom (constFn p A a) = constFn p B a := by
  apply TopCat.Presheaf.section_ext X.sheaf B
  intro y hy
  have hgs : ∀ {U : X.Opens} (hx : y ∈ U) (s : Γ(X, U)),
      gs (𝟙 X) y U s = (X.presheaf.germ U y hx).hom s := by
    intro U hx s
    unfold gs
    rw [dif_pos (show (𝟙 X : X ⟶ X) y ∈ U from hx)]
    rfl
  have hcst : ∀ {U : X.Opens} (hx : y ∈ U), (X.presheaf.germ U y hx).hom (constFn p U a) = cst p y a := by
    intro U hx
    rw [← hgs hx, gs_constFn p U (𝟙 X) y hx a, Category.id_comp]
  have e1 : (X.presheaf.germ B y hy).hom ((X.presheaf.map i.op).hom (constFn p A a)) =
      (X.presheaf.germ A y (i.le hy)).hom (constFn p A a) :=
    TopCat.Presheaf.germ_res_apply X.presheaf i y hy (constFn p A a)
  change (X.presheaf.germ B y hy).hom ((X.presheaf.map i.op).hom (constFn p A a)) =
    (X.presheaf.germ B y hy).hom (constFn p B a)
  rw [e1, hcst, hcst]
private theorem constFn_mul_left_cancel_of_flat [IsDomain V] (p : X ⟶ Sp V) [Flat p] {a : V} (ha : a ≠ 0) (U : X.Opens)
    (s t : Γ(X, U)) (hst : constFn p U a * s = constFn p U a * t) : s = t := by
  apply TopCat.Presheaf.section_ext X.sheaf U s t
  intro x hx
  apply cst_regular p x ha
  have hgs : gs (𝟙 X) x U (constFn p U a) = (X.presheaf.germ U x hx).hom (constFn p U a) := by
    unfold gs
    rw [dif_pos (show (𝟙 X : X ⟶ X) x ∈ U from hx)]
    rfl
  have hcst : (X.presheaf.germ U x hx).hom (constFn p U a) = cst p x a := by
    rw [← hgs, gs_constFn p U (𝟙 X) x hx a, Category.id_comp]
  have e := congrArg (X.presheaf.germ U x hx).hom hst
  rw [map_mul, map_mul, hcst] at e
  exact e
end ReciprocityTheory.ChartRestriction.G.Geo.Tor
end
end

set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open AlgebraicGeometry CategoryTheory Limits TopologicalSpace Opposite TensorProduct
open ReciprocityTheory.ChartRestriction.G.Semi
variable {V : Type} [CommRing V] {X Z : Scheme.{0}}
namespace ReciprocityTheory.ChartRestriction.G.Geo.Tor
theorem _root_.solution [IsDomain V] (p : X ⟶ Sp V) [Flat p] {a : V} (ha : a ≠ 0) {M : LB X} (s : LB.Sec M)
    (h : ∀ j, ∀ x ∈ M.U j, cst p x a ∣ gs (𝟙 X) x (M.U j) (s.f j)) :
    ∃ s' : LB.Sec M, ∀ j, s.f j = constFn p _ a * s'.f j := by
  choose g hg using fun j => exists_div p ha (M.U j) (s.f j) (h j)
  refine ⟨⟨g, fun i j => ?_⟩, hg⟩
  apply constFn_mul_left_cancel_of_flat p ha
  rw [← presheaf_map_constFn' p (homOfLE (inf_le_left : M.U i ⊓ M.U j ≤ M.U i)) a, ← map_mul, ← hg i, s.compat i j]
  conv_rhs => rw [presheaf_map_constFn', mul_left_comm,
    ← presheaf_map_constFn' p (homOfLE (inf_le_right : M.U i ⊓ M.U j ≤ M.U j)) a, ← map_mul, ← hg j]
end ReciprocityTheory.ChartRestriction.G.Geo.Tor
