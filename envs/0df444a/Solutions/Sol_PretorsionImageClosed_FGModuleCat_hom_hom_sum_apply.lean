-- Prove2me | solution 1 for PretorsionImageClosed.FGModuleCat.hom_hom_sum_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T01:42:13.087043+00:00
-- url     : https://prove2.me/submissions/781da2f0-1210-47ec-a19e-1a001b920e48

module
public import Mathlib.Algebra.Category.FGModuleCat.Abelian
public import Mathlib.Algebra.Category.FGModuleCat.Limits
public import Mathlib.Algebra.Category.FGModuleCat.Colimits
public import Mathlib.Algebra.Category.ModuleCat.EpiMono
public import Mathlib.CategoryTheory.Limits.Constructions.EpiMono
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Definitions.Def_PretorsionImageClosed_Modules_FiniteModules
public import Theorems.Thm_PretorsionImageClosed_FGModuleCat_hom_hom_sum

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
theorem _root_.solution {J : Type*} [Fintype J] {X Y : FGModuleCat R} (f : J → (X ⟶ Y))
    (x : X) : (∑ j, f j).hom.hom x = ∑ j, (f j).hom.hom x := by
  rw [hom_hom_sum, LinearMap.sum_apply]
end PretorsionImageClosed.FGModuleCat
