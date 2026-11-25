-- Prove2me | solution 1 for PretorsionImageClosed.FGModuleCat.range_eq_top_of_epi
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T01:08:49.631864+00:00
-- url     : https://prove2.me/submissions/dcd8e37b-7524-42b0-b294-e36b43f5bc3c

module
public import Mathlib.Algebra.Category.FGModuleCat.Abelian
public import Mathlib.Algebra.Category.FGModuleCat.Limits
public import Mathlib.Algebra.Category.FGModuleCat.Colimits
public import Mathlib.Algebra.Category.ModuleCat.EpiMono
public import Mathlib.CategoryTheory.Limits.Constructions.EpiMono
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Definitions.Def_PretorsionImageClosed_Modules_FiniteModules
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
theorem _root_.solution {X Y : FGModuleCat R} (f : X ⟶ Y) [Epi f] :
    LinearMap.range f.hom.hom = ⊤ :=
  LinearMap.range_eq_top.2 ((epi_iff_surjective f).1 inferInstance)
end PretorsionImageClosed.FGModuleCat
