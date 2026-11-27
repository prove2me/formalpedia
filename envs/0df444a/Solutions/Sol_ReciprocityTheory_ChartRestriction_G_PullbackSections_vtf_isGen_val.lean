-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.PullbackSections.vtf_isGen_val
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T05:29:01.014439+00:00
-- url     : https://prove2.me/submissions/de532191-bf3a-4f78-a15b-7e3ecf884eae

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_VtFrRdA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_VtfValPullGen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_vtf_val_lcg
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
theorem _root_.solution (φ : K → (Y ⟶ X)) (ε : K → ℤ) (t : LB.Gen (LB.LinComb L φ ε)) (ht : t.IsGen)
    (p : Sp ℂ ⟶ Y) (j j' : K → L.ι) (h : ⊤ ≤ p ⁻¹ᵁ (LB.wchart L φ j ⊓ LB.wchart L φ j')) :
    valAt' p _ (t.s j).val =
      (∏ k, valAt' (p ≫ φ k) (L.U (j k) ⊓ L.U (j' k)) (L.g (j k) (j' k)).val ^ ε k) *
        valAt' p _ (t.s j').val := by
  have h' : ⊤ ≤ p ⁻¹ᵁ ((LB.LinComb L φ ε).U j ⊓ (LB.LinComb L φ ε).U j') := h
  calc valAt' p _ (t.s j).val
      = valAt' p ((LB.LinComb L φ ε).U j ⊓ (LB.LinComb L φ ε).U j')
          (res (inf_le_left : (LB.LinComb L φ ε).U j ⊓ (LB.LinComb L φ ε).U j' ≤ _) (t.s j)).val :=
        (vtf_val_res p _ h' _).symm
    _ = valAt' p ((LB.LinComb L φ ε).U j ⊓ (LB.LinComb L φ ε).U j')
          ((LB.LinComb L φ ε).g j j' *
            res (inf_le_right : (LB.LinComb L φ ε).U j ⊓ (LB.LinComb L φ ε).U j' ≤ _) (t.s j')).val := by
        rw [ht j j']
    _ = valAt' p ((LB.LinComb L φ ε).U j ⊓ (LB.LinComb L φ ε).U j') ((LB.LinComb L φ ε).g j j').val *
          valAt' p ((LB.LinComb L φ ε).U j ⊓ (LB.LinComb L φ ε).U j')
            (res (inf_le_right : (LB.LinComb L φ ε).U j ⊓ (LB.LinComb L φ ε).U j' ≤ _) (t.s j')).val := by
        rw [Units.val_mul, valAt'_mul]
    _ = _ := by rw [vtf_val_lcg L φ ε p j j' h, vtf_val_res p _ h']
end ReciprocityTheory.ChartRestriction.G.PullbackSections
