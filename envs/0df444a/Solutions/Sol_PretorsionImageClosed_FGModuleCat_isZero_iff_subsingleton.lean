-- Prove2me | solution 1 for PretorsionImageClosed.FGModuleCat.isZero_iff_subsingleton
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T00:34:48.088676+00:00
-- url     : https://prove2.me/submissions/4dc42875-b117-4b04-a648-4183316b96f0

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
namespace PretorsionImageClosed.FGModuleCat
theorem _root_.solution (X : FGModuleCat R) : IsZero X ↔ Subsingleton X := by
  rw [IsZero.iff_id_eq_zero]
  constructor
  · intro h
    refine ⟨fun x y => ?_⟩
    have hx : x = 0 := congrArg (fun g : X ⟶ X => g.hom.hom x) h
    have hy : y = 0 := congrArg (fun g : X ⟶ X => g.hom.hom y) h
    rw [hx, hy]
  · intro h
    ext x
    exact Subsingleton.elim _ _
end PretorsionImageClosed.FGModuleCat
