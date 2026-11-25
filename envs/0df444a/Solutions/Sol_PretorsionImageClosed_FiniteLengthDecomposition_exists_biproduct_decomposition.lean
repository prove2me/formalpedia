-- Prove2me | solution 1 for PretorsionImageClosed.FiniteLengthDecomposition.exists_biproduct_decomposition
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T05:19:28.329867+00:00
-- url     : https://prove2.me/submissions/056257ec-fdd7-4598-88f2-df95b072efb3

module
public import Mathlib.Algebra.Category.ModuleCat.Biproducts
public import Mathlib.CategoryTheory.FintypeCat
public import Mathlib.RingTheory.Length
public import Mathlib.Tactic.Ring
public import Definitions.Def_PretorsionImageClosed_IndecomposableClosures_Skeleton
public import Definitions.Def_PretorsionImageClosed_IndecomposableClosures_Decomposition

set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open CategoryTheory CategoryTheory.Limits
open PretorsionImageClosed PretorsionImageClosed.FiniteLengthDecomposition
universe u w
variable {R : Type u} [Ring R] [IsNoetherianRing R]
attribute [local instance]
  HasFiniteBiproducts.of_hasFiniteCoproducts
namespace PretorsionImageClosed.FiniteLengthDecomposition
theorem _root_.solution
    (X : FGModuleCat.{w} R) (hfinite : IsFiniteLength R X) :
    ∃ (J : FintypeCat.{0}) (Y : J → FGModuleCat.{w} R),
      (∀ j, PretorsionImageClosed.IsIndecomposableModule R (Y j)) ∧
      Nonempty (X ≅ biproduct Y) := by
  let d := piDecomposition X hfinite
  exact ⟨d.index, d.summand, d.indecomposable,
    ⟨d.toBiproductIso⟩⟩
end PretorsionImageClosed.FiniteLengthDecomposition
