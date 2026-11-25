-- Prove2me | solution 1 for PretorsionImageClosed.FGModuleCat.hom_hom_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T01:37:49.967513+00:00
-- url     : https://prove2.me/submissions/adfeb25e-b08c-4315-bf48-736139c228e4

module
public import Mathlib.Algebra.Category.FGModuleCat.Abelian
public import Mathlib.Algebra.Category.FGModuleCat.Limits
public import Mathlib.Algebra.Category.FGModuleCat.Colimits
public import Mathlib.Algebra.Category.ModuleCat.EpiMono
public import Mathlib.CategoryTheory.Limits.Constructions.EpiMono
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Definitions.Def_PretorsionImageClosed_Modules_FiniteModules

set_option autoImplicit true
@[expose] public section
public section
set_option autoImplicit false
noncomputable section
open PretorsionImageClosed
open CategoryTheory Limits
open PretorsionImageClosed.FGModuleCat
variable {R : Type*} [Ring R] [IsNoetherianRing R]
omit [IsNoetherianRing R]
namespace PretorsionImageClosed.FGModuleCat
theorem _root_.solution {J : Type*} [Fintype J] {X Y : FGModuleCat R} (f : J → (X ⟶ Y)) :
    (∑ j, f j).hom.hom = ∑ j, (f j).hom.hom := by
  have h : (∑ j, f j).hom = ∑ j, (f j).hom :=
    map_sum (InducedCategory.homAddEquiv : (X ⟶ Y) ≃+ (X.obj ⟶ Y.obj)) f Finset.univ
  rw [h, ModuleCat.hom_sum]
end PretorsionImageClosed.FGModuleCat
