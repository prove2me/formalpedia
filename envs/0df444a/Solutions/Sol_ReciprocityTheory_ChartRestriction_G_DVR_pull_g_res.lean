-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.DVR.pull_g_res
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:48:33.002826+00:00
-- url     : https://prove2.me/submissions/af45053c-abc3-4273-97f8-e43274b22a6e

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ProdIso
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_NonzeroLocus
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_GenAmple
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace
namespace ReciprocityTheory.ChartRestriction.G.DVR
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
section Flat
variable {Y X₁ X₂ : Scheme.{0}} (L₁ : LB X₁) (L₂ : LB X₂) (f₁ : Y ⟶ X₁) (f₂ : Y ⟶ X₂)
private lemma res_res_lemma {X : Scheme.{0}} {U V W : X.Opens} (h1 : W ≤ V) (h2 : V ≤ U) (u : Γ(X, U)ˣ) :
    res h1 (res h2 u) = res (h1.trans h2) u := by
  apply Units.ext
  show (X.presheaf.map (homOfLE h1).op).hom ((X.presheaf.map (homOfLE h2).op).hom (u : Γ(X, U))) =
    (X.presheaf.map ((homOfLE h2).op ≫ (homOfLE h1).op)).hom (u : Γ(X, U))
  rw [Functor.map_comp]
  rfl
end Flat
section NZ
variable {Y : Scheme.{0}}
end NZ
section Main
variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
end Main
end ReciprocityTheory.ChartRestriction.G.DVR
end
end

set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.DVR
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
variable {Y X₁ X₂ : Scheme.{0}} (L₁ : LB X₁) (L₂ : LB X₂) (f₁ : Y ⟶ X₁) (f₂ : Y ⟶ X₂)
namespace ReciprocityTheory.ChartRestriction.G.DVR
theorem _root_.solution {X : Scheme.{0}} (L : LB X) (f : Y ⟶ X) (a b : PUnit → L.ι) {V : Y.Opens}
    (h : V ≤ (L.pull f).U a ⊓ (L.pull f).U b) : res h ((L.pull f).g a b) = tr L V f (a PUnit.unit) (b PUnit.unit) := by
  have hV : V ≤ f ⁻¹ᵁ (L.U (a PUnit.unit) ⊓ L.U (b PUnit.unit)) := by
    intro x hx
    have hx' := h hx
    simp only [LB.pull, LB.LinComb, LB.wchart, TopologicalSpace.Opens.mem_inf, TopologicalSpace.Opens.mem_mk,
      Set.mem_iInter, Set.mem_preimage, SetLike.mem_coe] at hx'
    exact ⟨hx'.1 PUnit.unit, hx'.2 PUnit.unit⟩
  unfold tr
  rw [dif_pos hV]
  dsimp only [LB.pull, LB.LinComb]
  rw [Fintype.prod_unique, zpow_one]
  exact (res_res_lemma h _ _).trans rfl
end ReciprocityTheory.ChartRestriction.G.DVR
