-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.PullbackSections.vtf_corr_val
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T05:28:56.230816+00:00
-- url     : https://prove2.me/submissions/a8420b85-7f1e-4859-8723-84cb9f5d9dbf

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_VtFrRdA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_VtfValPullGen
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
theorem _root_.solution (φ : K → (Y ⟶ X)) (ε : K → ℤ) (φ' : K' → (Y ⟶ X)) (ε' : K' → ℤ)
    (t : LB.Gen (LB.LinComb L φ ε)) (t' : LB.Gen (LB.LinComb L φ' ε')) (hc : LB.Gen.Corr L φ ε φ' ε' t t')
    (j : K → L.ι) (j' : K' → L.ι) (hj : LB.Coh L φ j) (hj' : LB.Coh L φ' j')
    (hjj : ∀ k k', φ k = φ' k' → j k = j' k') (p : Sp ℂ ⟶ Y)
    (h : ⊤ ≤ p ⁻¹ᵁ (LB.wchart L φ j ⊓ LB.wchart L φ' j')) :
    valAt' p _ (t.s j).val = valAt' p _ (t'.s j').val := by
  calc valAt' p _ (t.s j).val
      = valAt' p (LB.wchart L φ j ⊓ LB.wchart L φ' j')
          (res (inf_le_left : LB.wchart L φ j ⊓ LB.wchart L φ' j' ≤ LB.wchart L φ j) (t.s j)).val :=
        (vtf_val_res p _ h _).symm
    _ = valAt' p (LB.wchart L φ j ⊓ LB.wchart L φ' j')
          (res (inf_le_right : LB.wchart L φ j ⊓ LB.wchart L φ' j' ≤ LB.wchart L φ' j') (t'.s j')).val := by
        rw [hc j j' hj hj' hjj]
    _ = _ := vtf_val_res p _ h _
end ReciprocityTheory.ChartRestriction.G.PullbackSections
