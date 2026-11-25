-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Out.CubePf.prod_sameSum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T13:16:43.787001+00:00
-- url     : https://prove2.me/submissions/df9da55b-0a50-4ed0-89a4-0b7163ee8315

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GtBaseChangeSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_DegProd
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_GeneratorPullback_PullAlong
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniformBaseChange_Transport
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_TangentLinearity_ConstPullback
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_CubePullbacks_Transfer
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_Out_CubePf_zpow_sum__eeea0ab3dee3

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
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj
  AlgebraicGeometry
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Out.CubePf
open Semi
namespace ReciprocityTheory.ChartRestriction.G.Out.CubePf
theorem _root_.solution {M : Type} [CommGroup M] {Y X : Scheme.{0}} {K K' : Type} [Fintype K]
    [Fintype K'] (B : (Y ⟶ X) → M) (ψ : K → (Y ⟶ X)) (ψ' : K' → (Y ⟶ X)) (ε : K → ℤ)
    (ε' : K' → ℤ) (hS : LB.SameSum ψ ε ψ' ε') :
    ∏ k, B (ψ k) ^ ε k = ∏ k', B (ψ' k') ^ ε' k' := by
  classical
  have key : ∀ {L : Type} [Fintype L] (g : L → (Y ⟶ X)) (e : L → ℤ) (S : Finset (Y ⟶ X)),
      (∀ k, g k ∈ S) → ∏ k, B (g k) ^ e k = ∏ φ ∈ S, B φ ^ (∑ k, if g k = φ then e k else 0) := by
    intro L _ g e S hS
    rw [← Finset.prod_fiberwise_of_maps_to (g := g) (t := S) (fun k _ => hS k)]
    refine Finset.prod_congr rfl (fun φ _ => ?_)
    rw [zpow_sum', Finset.prod_filter]
    refine Finset.prod_congr rfl (fun k _ => ?_)
    split_ifs with hk
    · rw [hk]
    · simp
  rw [key ψ ε (Finset.univ.image ψ ∪ Finset.univ.image ψ')
      (fun k => Finset.mem_union_left _ (Finset.mem_image_of_mem _ (Finset.mem_univ _))),
    key ψ' ε' (Finset.univ.image ψ ∪ Finset.univ.image ψ')
      (fun k => Finset.mem_union_right _ (Finset.mem_image_of_mem _ (Finset.mem_univ _)))]
  refine Finset.prod_congr rfl (fun φ _ => ?_)
  congr 1
  first
  | exact hS φ
  | convert hS φ
end ReciprocityTheory.ChartRestriction.G.Out.CubePf
