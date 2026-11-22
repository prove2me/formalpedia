-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Geo.Tor.glue_unit
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:18:57.509848+00:00
-- url     : https://prove2.me/submissions/a6aa290a-2b47-4943-b38d-1043f1bee523

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_OneArcSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_PullCub
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_val

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open AlgebraicGeometry CategoryTheory Limits TopologicalSpace Opposite
open ReciprocityTheory.ChartRestriction.G.Semi
variable {X Y Z : Scheme.{0}}
namespace ReciprocityTheory.ChartRestriction.G.Geo.Tor
theorem _root_.solution {J : Type} (V : X.Opens) (W : J → X.Opens) (hW : ∀ i, W i ≤ V) (hc : V ≤ iSup W)
    (u : ∀ i, Γ(X, W i)ˣ)
    (h : ∀ i j, ∀ x ∈ W i ⊓ W j, gm (𝟙 X) x (W i) (u i) = gm (𝟙 X) x (W j) (u j)) :
    ∃ s : Γ(X, V)ˣ, ∀ i, res (hW i) s = u i := by
  have comp : ∀ t : ∀ i, Γ(X, W i)ˣ,
      (∀ i j, ∀ x ∈ W i ⊓ W j, gm (𝟙 X) x (W i) (t i) = gm (𝟙 X) x (W j) (t j)) →
      TopCat.Presheaf.IsCompatible X.sheaf.1 W (fun i => ((t i : Γ(X, W i)ˣ) : Γ(X, W i))) := by
    intro t ht i j
    apply TopCat.Presheaf.section_ext X.sheaf (W i ⊓ W j)
    intro x hx
    have e := congrArg Units.val (ht i j x hx)
    rw [gm_val _ _ _ hx.1, gm_val _ _ _ hx.2] at e
    erw [TopCat.Presheaf.germ_res_apply, TopCat.Presheaf.germ_res_apply]
    exact e
  have hinv : ∀ i j, ∀ x ∈ W i ⊓ W j, gm (𝟙 X) x (W i) (u i)⁻¹ = gm (𝟙 X) x (W j) (u j)⁻¹ := by
    intro i j x hx
    rw [map_inv, map_inv, h i j x hx]
  obtain ⟨s, hs, -⟩ := TopCat.Sheaf.existsUnique_gluing' X.sheaf W V (fun i => homOfLE (hW i)) hc _
    (comp u h)
  obtain ⟨s', hs', -⟩ := TopCat.Sheaf.existsUnique_gluing' X.sheaf W V (fun i => homOfLE (hW i)) hc _
    (comp (fun i => (u i)⁻¹) hinv)
  have hss : s * s' = 1 := by
    apply TopCat.Presheaf.section_ext X.sheaf V
    intro x hx
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 (hc hx)
    have a1 := congrArg (X.sheaf.presheaf.germ (W i) x hi) (hs i)
    have a2 := congrArg (X.sheaf.presheaf.germ (W i) x hi) (hs' i)
    rw [TopCat.Presheaf.germ_res_apply] at a1 a2
    rw [map_mul, map_one, a1, a2]
    have e := congrArg (X.sheaf.presheaf.germ (W i) x hi) (Units.mul_inv (u i))
    exact (map_mul _ _ _).symm.trans (e.trans (map_one _))
  refine ⟨⟨s, s', hss, (mul_comm s' s).trans hss⟩, fun i => Units.ext ?_⟩
  exact hs i
end ReciprocityTheory.ChartRestriction.G.Geo.Tor
