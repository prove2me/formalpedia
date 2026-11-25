-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.DVR.loc_div
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T13:02:15.914606+00:00
-- url     : https://prove2.me/submissions/fa4e1074-1cff-4b84-a14b-8f60aaa20ca0

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DivCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ThickKer
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gs_constFn


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.DVR
open AlgebraicGeometry CategoryTheory Limits TopologicalSpace Opposite ReciprocityTheory.ChartRestriction.G.Geo.Tor
variable {V : Type} [CommRing V] {X : Scheme.{0}}
namespace ReciprocityTheory.ChartRestriction.G.DVR
theorem _root_.solution {P : Scheme.{0}} (p' : P ⟶ Sp V) (W : P.Opens) (f : Γ(P, W)) (r : V) (x : P) (hx : x ∈ W)
    (h : cst p' x r ∣ gs (𝟙 P) x W f) : ∃ (U : P.Opens) (_ : U ≤ W) (_ : x ∈ U) (g : Γ(P, U)),
      ∀ y ∈ U, gs (𝟙 P) y W f = cst p' y r * gs (𝟙 P) y U g := by
  obtain ⟨t, ht⟩ := h
  obtain ⟨U, hU, g, rfl⟩ := P.presheaf.exists_germ_eq t
  have hm : x ∈ W ⊓ U := ⟨hx, hU⟩
  have e : gs (𝟙 P) x (W ⊓ U) ((P.presheaf.map (homOfLE inf_le_left).op).hom f) =
      gs (𝟙 P) x (W ⊓ U) (constFn p' (W ⊓ U) r * (P.presheaf.map (homOfLE inf_le_right).op).hom g) := by
    rw [gs_res _ x _ hm, gs_mul _ x _ hm, gs_res _ x _ hm, gs_constFn p' _ _ x hm, Category.id_comp, ht,
      gs_eq _ x U hU]
    rfl
  rw [gs_eq _ x _ hm, gs_eq _ x _ hm] at e
  obtain ⟨U', hU', i₁, i₂, e'⟩ := P.presheaf.germ_eq x hm hm _ _ e
  have le : U' ≤ W ⊓ U := i₁.le
  refine ⟨U', le.trans inf_le_left, hU', (P.presheaf.map (homOfLE (le.trans inf_le_right)).op).hom g, fun y hy => ?_⟩
  have e'' := congrArg (gs (𝟙 P) y U') e'
  have k := (gs_res (𝟙 P) y le hy _).symm.trans (e''.trans (gs_res (𝟙 P) y le hy _))
  have hy' : (𝟙 P : P ⟶ P) y ∈ W ⊓ U := le hy
  have k' : gs (𝟙 P) y (W ⊓ U) ((P.presheaf.map (homOfLE inf_le_left).op).hom f) =
      gs (𝟙 P) y (W ⊓ U) (constFn p' (W ⊓ U) r * (P.presheaf.map (homOfLE inf_le_right).op).hom g) := k
  rw [gs_res _ y _ hy', gs_mul _ y _ hy', gs_res _ y _ hy', gs_constFn p' _ _ y hy', Category.id_comp] at k'
  rw [k', gs_res _ y _ hy]
end ReciprocityTheory.ChartRestriction.G.DVR
