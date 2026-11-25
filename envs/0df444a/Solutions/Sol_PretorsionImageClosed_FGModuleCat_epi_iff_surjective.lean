-- Prove2me | solution 1 for PretorsionImageClosed.FGModuleCat.epi_iff_surjective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T00:44:16.668001+00:00
-- url     : https://prove2.me/submissions/b4cf9159-0ea7-4f70-8a8b-8351f4b04d6c

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
theorem _root_.solution {X Y : FGModuleCat R} (f : X ⟶ Y) : Epi f ↔ Function.Surjective f.hom.hom := by
  constructor
  · intro hf
    have : Epi ((forget₂ (FGModuleCat R) (ModuleCat R)).map f) := inferInstance
    exact (ModuleCat.epi_iff_surjective _).1 this
  · intro hf
    have : Epi ((forget₂ (FGModuleCat R) (ModuleCat R)).map f) :=
      (ModuleCat.epi_iff_surjective _).2 hf
    exact (forget₂ (FGModuleCat R) (ModuleCat R)).epi_of_epi_map this
end PretorsionImageClosed.FGModuleCat
