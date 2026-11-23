-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Geo.Tor.exists_div
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:27:46.337686+00:00
-- url     : https://prove2.me/submissions/4e59ffa2-404c-42ed-b463-6d124b151d80

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsLieBasis
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DivCalc
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gs_constFn
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_cst_regular

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open AlgebraicGeometry CategoryTheory Limits TopologicalSpace Opposite TensorProduct
open ReciprocityTheory.ChartRestriction.G.Semi
variable {V : Type} [CommRing V] {X Z : Scheme.{0}}
namespace ReciprocityTheory.ChartRestriction.G.Geo.Tor
theorem _root_.solution [IsDomain V] (p : X ⟶ Sp V) [Flat p] {a : V} (ha : a ≠ 0) (W : X.Opens) (f : Γ(X, W))
    (h : ∀ x ∈ W, cst p x a ∣ gs (𝟙 X) x W f) : ∃ g : Γ(X, W), f = constFn p W a * g := by
  classical
  have hgs : ∀ {U : X.Opens} (x : X) (hx : x ∈ U) (s : Γ(X, U)),
      gs (𝟙 X) x U s = (X.presheaf.germ U x hx).hom s := by
    intro U x hx s
    unfold gs
    rw [dif_pos (show (𝟙 X : X ⟶ X) x ∈ U from hx)]
    rfl
  have hcst : ∀ {U : X.Opens} (x : X) (hx : x ∈ U),
      (X.presheaf.germ U x hx).hom (constFn p U a) = cst p x a := by
    intro U x hx
    rw [← hgs x hx, gs_constFn p U (𝟙 X) x hx a, Category.id_comp]
  have hmap : ∀ {A B : X.Opens} (i j : A ⟶ B) (s : Γ(X, B)),
      (X.presheaf.map i.op).hom s = (X.presheaf.map j.op).hom s := by
    intro A B i j s
    rw [Subsingleton.elim i j]
  have hmapc : ∀ {A B C : X.Opens} (i : A ⟶ B) (j : B ⟶ C) (s : Γ(X, C)),
      (X.presheaf.map i.op).hom ((X.presheaf.map j.op).hom s) = (X.presheaf.map (i ≫ j).op).hom s := by
    intro A B C i j s
    rw [op_comp, Functor.map_comp]
    rfl
  have hres : ∀ {U V : X.Opens} (i : V ⟶ U),
      (X.presheaf.map i.op).hom (constFn p U a) = constFn p V a := by
    intro U V i
    apply TopCat.Presheaf.section_ext X.sheaf V
    intro y hy
    have e1 := TopCat.Presheaf.germ_res_apply X.presheaf i y hy (constFn p U a)
    have e2 := hcst y hy
    have e3 := hcst (U := U) y (i.le hy)
    exact e1.trans (e3.trans e2.symm)
  have hcancel : ∀ (U : X.Opens) (s t : Γ(X, U)), constFn p U a * s = constFn p U a * t → s = t := by
    intro U s t hst
    apply TopCat.Presheaf.section_ext X.sheaf U s t
    intro x hx
    apply cst_regular p x ha
    have e := congrArg (X.presheaf.germ U x hx).hom hst
    rw [map_mul, map_mul, hcst x hx] at e
    exact e
  have hloc : ∀ y : W, ∃ (U : X.Opens) (_ : (y : X) ∈ U) (iU : U ⟶ W) (g : Γ(X, U)),
      (X.presheaf.map iU.op).hom f = constFn p U a * g := by
    rintro ⟨x, hx⟩
    obtain ⟨c, hc⟩ := h x hx
    obtain ⟨U₁, hx₁, g₁, hg₁⟩ := TopCat.Presheaf.germ_exist X.presheaf c
    have he : (X.presheaf.germ W x hx).hom f = (X.presheaf.germ U₁ x hx₁).hom (constFn p U₁ a * g₁) := by
      rw [map_mul, hcst x hx₁, ← hgs x hx, hc]
      exact congrArg _ hg₁.symm
    obtain ⟨U, hxU, iW, i1, heq⟩ := TopCat.Presheaf.germ_eq X.presheaf x hx hx₁ f _ he
    refine ⟨U, hxU, iW, (X.presheaf.map i1.op).hom g₁, ?_⟩
    rw [heq, map_mul, hres]
  choose U hxU iU g hg using hloc
  have hcomp : TopCat.Presheaf.IsCompatible X.presheaf U g := by
    intro x y
    apply hcancel
    rw [← hres (TopologicalSpace.Opens.infLELeft (U x) (U y)), ← map_mul, ← hg x, hmapc]
    conv_rhs => rw [hres, ← hres (TopologicalSpace.Opens.infLERight (U x) (U y)), ← map_mul, ← hg y, hmapc]
    exact hmap _ _ f
  obtain ⟨g', hg', -⟩ := TopCat.Sheaf.existsUnique_gluing' X.sheaf U W iU
    (fun x hx => TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨x, hx⟩, hxU _⟩) g hcomp
  obtain ⟨g'', hg''⟩ : ∃ g'' : Γ(X, W), ∀ i, (X.presheaf.map (iU i).op).hom g'' = g i := ⟨g', hg'⟩
  refine ⟨g'', ?_⟩
  apply TopCat.Presheaf.section_ext X.sheaf W
  intro x hx
  have e1 : (X.presheaf.germ (U ⟨x, hx⟩) x (hxU _)).hom ((X.presheaf.map (iU ⟨x, hx⟩).op).hom f) =
      (X.presheaf.germ W x hx).hom f :=
    TopCat.Presheaf.germ_res_apply X.presheaf (iU ⟨x, hx⟩) x (hxU _) f
  have e2 : (X.presheaf.germ (U ⟨x, hx⟩) x (hxU _)).hom
      ((X.presheaf.map (iU ⟨x, hx⟩).op).hom (constFn p W a * g'')) =
      (X.presheaf.germ W x hx).hom (constFn p W a * g'') :=
    TopCat.Presheaf.germ_res_apply X.presheaf (iU ⟨x, hx⟩) x (hxU _) (constFn p W a * g'')
  change (X.presheaf.germ W x hx).hom f = (X.presheaf.germ W x hx).hom (constFn p W a * g'')
  rw [← e1, ← e2, hg, map_mul (X.presheaf.map (iU ⟨x, hx⟩).op).hom, hres, hg'']
end ReciprocityTheory.ChartRestriction.G.Geo.Tor
