-- Prove2me | solution 1 for PretorsionImageClosed.FGModuleCat.mono_iff_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T00:34:18.29347+00:00
-- url     : https://prove2.me/submissions/de9c0686-43f7-49f2-923d-fe53bc147811

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
theorem _root_.solution {X Y : FGModuleCat R} (f : X ⟶ Y) : Mono f ↔ Function.Injective f.hom.hom := by
  constructor
  · intro hf
    have : Mono ((forget₂ (FGModuleCat R) (ModuleCat R)).map f) := inferInstance
    exact (ModuleCat.mono_iff_injective _).1 this
  · intro hf
    have : Mono ((forget₂ (FGModuleCat R) (ModuleCat R)).map f) :=
      (ModuleCat.mono_iff_injective _).2 hf
    exact (forget₂ (FGModuleCat R) (ModuleCat R)).mono_of_mono_map this
end PretorsionImageClosed.FGModuleCat
