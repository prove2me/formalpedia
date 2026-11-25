-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.PullbackSections.vtf_val_lcg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T16:05:09.138435+00:00
-- url     : https://prove2.me/submissions/174e3c27-ce75-41b6-b5af-0cf5a99d1577

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_VtFrRdA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_VtfValPullGen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_vtf_val_prodU
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_vtf_val_pullU
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_vtf_val_res


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
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.PullbackSections
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Opposite
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.TB.ValAt Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory
variable {X Y Z : Scheme.{0}} (L : LB X) {K K' : Type} [Fintype K] [Fintype K']
namespace ReciprocityTheory.ChartRestriction.G.PullbackSections
theorem _root_.solution (φ : K → (Y ⟶ X)) (ε : K → ℤ) (p : Sp ℂ ⟶ Y) (j j' : K → L.ι)
    (h : ⊤ ≤ p ⁻¹ᵁ (LB.wchart L φ j ⊓ LB.wchart L φ j')) :
    valAt' p _ ((LB.LinComb L φ ε).g j j').val =
      ∏ k, valAt' (p ≫ φ k) (L.U (j k) ⊓ L.U (j' k)) (L.g (j k) (j' k)).val ^ ε k := by
  calc valAt' p _ ((LB.LinComb L φ ε).g j j').val
      = valAt' p (LB.wchart L φ j ⊓ LB.wchart L φ j')
          (∏ k, (res (le_inf (inf_le_left.trans (LB.wchart_le L φ j k))
            (inf_le_right.trans (LB.wchart_le L φ j' k)) :
              LB.wchart L φ j ⊓ LB.wchart L φ j' ≤ φ k ⁻¹ᵁ (L.U (j k) ⊓ L.U (j' k)))
            (pullU (φ k) _ (L.g (j k) (j' k)))) ^ ε k).val := rfl
    _ = ∏ k, valAt' p (LB.wchart L φ j ⊓ LB.wchart L φ j')
          (res (le_inf (inf_le_left.trans (LB.wchart_le L φ j k))
            (inf_le_right.trans (LB.wchart_le L φ j' k)) :
              LB.wchart L φ j ⊓ LB.wchart L φ j' ≤ φ k ⁻¹ᵁ (L.U (j k) ⊓ L.U (j' k)))
            (pullU (φ k) _ (L.g (j k) (j' k)))).val ^ ε k := vtf_val_prodU p h _ ε
    _ = _ := Finset.prod_congr rfl fun k _ => by
        exact congrArg (· ^ ε k) ((vtf_val_res (U := φ k ⁻¹ᵁ (L.U (j k) ⊓ L.U (j' k))) p _ h _).trans
          (vtf_val_pullU p (φ k) (L.U (j k) ⊓ L.U (j' k)) (L.g (j k) (j' k))))
end ReciprocityTheory.ChartRestriction.G.PullbackSections
