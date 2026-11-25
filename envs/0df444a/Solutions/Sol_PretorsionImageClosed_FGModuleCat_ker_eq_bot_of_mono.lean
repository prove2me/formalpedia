-- Prove2me | solution 1 for PretorsionImageClosed.FGModuleCat.ker_eq_bot_of_mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T01:37:37.393799+00:00
-- url     : https://prove2.me/submissions/be2f54ce-1c84-4582-826a-da047405abc0

module
public import Mathlib.Algebra.Category.FGModuleCat.Abelian
public import Mathlib.Algebra.Category.FGModuleCat.Limits
public import Mathlib.Algebra.Category.FGModuleCat.Colimits
public import Mathlib.Algebra.Category.ModuleCat.EpiMono
public import Mathlib.CategoryTheory.Limits.Constructions.EpiMono
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Definitions.Def_PretorsionImageClosed_Modules_FiniteModules
public import Theorems.Thm_PretorsionImageClosed_FGModuleCat_mono_iff_injective

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
theorem _root_.solution {X Y : FGModuleCat R} (f : X ⟶ Y) [Mono f] :
    LinearMap.ker f.hom.hom = ⊥ :=
  LinearMap.ker_eq_bot.2 ((mono_iff_injective f).1 inferInstance)
end PretorsionImageClosed.FGModuleCat
