-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Semi.TorusInj.eq_zero_of_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T13:45:17.20235+00:00
-- url     : https://prove2.me/submissions/05de84f8-bec3-433d-a387-211df60d6586

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_AbelianSchemeQuotients_QSurjective
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_WeightedChartPullback_TorusInj
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Semi_TorusInj_ev_snd
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Semi_TorusInj_ev_chi
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Semi_TorusInj_coeff_sum_single

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory
open scoped AlgebraMonoidAlgebra
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Semi.TorusInj
variable {S : Scheme.{0}} (X : Type) [AddCommGroup X] (Y : Over S)
namespace ReciprocityTheory.ChartRestriction.G.Semi.TorusInj
theorem _root_.solution {V : Y.left.Opens} (s : Finset X) (h : X → Γ(Y.left, V))
    (hs : ∑ χ ∈ s, ((splitTorus S X ⊗ Y).left.presheaf.map (homOfLE le_top).op).hom (chiP X Y χ) *
      ((snd (splitTorus S X) Y).left.app V).hom (h χ) = 0) :
    ∀ χ ∈ s, h χ = 0 := by
  intro χ₀ hχ₀
  refine TopCat.Presheaf.section_ext Y.left.sheaf V (h χ₀) 0 fun x hx => ?_
  obtain ⟨W, hW, hxW, hWV⟩ : ∃ W : Y.left.Opens, IsAffineOpen W ∧ x ∈ W ∧ W ≤ V := by
    obtain ⟨_, ⟨W, hW, rfl⟩, hxW, hWV⟩ := (Y.left.isBasis_affineOpens).exists_subset_of_mem_open hx V.2
    exact ⟨W, hW, hxW, hWV⟩
  have hle : (snd (splitTorus S X) Y).left ⁻¹ᵁ W ≤ (snd (splitTorus S X) Y).left ⁻¹ᵁ V :=
    fun y hy => hWV hy
  have e1 : ∀ χ : X, ((splitTorus S X ⊗ Y).left.presheaf.map (homOfLE hle).op).hom
      (((splitTorus S X ⊗ Y).left.presheaf.map (homOfLE le_top).op).hom (chiP X Y χ)) =
      ((splitTorus S X ⊗ Y).left.presheaf.map (homOfLE le_top).op).hom (chiP X Y χ) := by
    intro c; rw [← CommRingCat.comp_apply, ← Functor.map_comp]; rfl
  have e2 : ∀ c : Γ(Y.left, V), ((splitTorus S X ⊗ Y).left.presheaf.map (homOfLE hle).op).hom
      (((snd (splitTorus S X) Y).left.app V).hom c) =
      ((snd (splitTorus S X) Y).left.app W).hom ((Y.left.presheaf.map (homOfLE hWV).op).hom c) := by
    intro c
    rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, Scheme.Hom.app_eq_appLE,
      Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_map, Scheme.Hom.map_appLE]
  have hres := congrArg ((splitTorus S X ⊗ Y).left.presheaf.map (homOfLE hle).op).hom hs
  simp only [map_sum, map_mul, map_zero, e1, e2] at hres
  have hev := congrArg (ev hW) hres
  simp only [map_sum, map_mul, map_zero, ev_chi, ev_snd, AddMonoidAlgebra.single_mul_single,
    add_zero, one_mul] at hev
  have hc := congrArg (fun f => f.coeff χ₀) hev
  rw [coeff_sum_single X s _ χ₀ hχ₀, AddMonoidAlgebra.coeff_zero, Finsupp.coe_zero, Pi.zero_apply] at hc
  have hg := TopCat.Presheaf.germ_res_apply Y.left.presheaf (homOfLE hWV) x hxW (h χ₀)
  rw [hc, map_zero] at hg
  exact hg.symm.trans (map_zero _).symm
end ReciprocityTheory.ChartRestriction.G.Semi.TorusInj
