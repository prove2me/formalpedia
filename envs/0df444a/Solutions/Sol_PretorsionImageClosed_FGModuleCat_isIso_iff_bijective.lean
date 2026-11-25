-- Prove2me | solution 1 for PretorsionImageClosed.FGModuleCat.isIso_iff_bijective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T01:08:47.257795+00:00
-- url     : https://prove2.me/submissions/a7ad3993-de0d-4c78-8553-6f9202ab78d4

module
public import Mathlib.Algebra.Category.FGModuleCat.Abelian
public import Mathlib.Algebra.Category.FGModuleCat.Limits
public import Mathlib.Algebra.Category.FGModuleCat.Colimits
public import Mathlib.Algebra.Category.ModuleCat.EpiMono
public import Mathlib.CategoryTheory.Limits.Constructions.EpiMono
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Definitions.Def_PretorsionImageClosed_Modules_FiniteModules
public import Theorems.Thm_PretorsionImageClosed_FGModuleCat_mono_iff_injective
public import Theorems.Thm_PretorsionImageClosed_FGModuleCat_epi_iff_surjective

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
theorem _root_.solution {X Y : FGModuleCat R} (f : X ⟶ Y) : IsIso f ↔ Function.Bijective f.hom.hom := by
  constructor
  · intro hf
    exact ⟨(mono_iff_injective f).1 inferInstance, (epi_iff_surjective f).1 inferInstance⟩
  · rintro ⟨hi, hs⟩
    haveI := (mono_iff_injective f).2 hi
    haveI := (epi_iff_surjective f).2 hs
    exact isIso_of_mono_of_epi f
end PretorsionImageClosed.FGModuleCat
