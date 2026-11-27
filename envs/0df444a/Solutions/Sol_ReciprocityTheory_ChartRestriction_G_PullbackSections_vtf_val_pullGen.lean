-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.PullbackSections.vtf_val_pullGen
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T05:34:53.22088+00:00
-- url     : https://prove2.me/submissions/3d019860-5880-4fe2-a2bd-e9e082af8584

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_VtFrRdA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_VtfValPullGen
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
theorem _root_.solution (φ : K → (Y ⟶ X)) (ε : K → ℤ) (c : LB.Gen (LB.LinComb L φ ε)) (h : Z ⟶ Y)
    (p : Sp ℂ ⟶ Z) (j : K → L.ι) (hp : ⊤ ≤ p ⁻¹ᵁ LB.wchart L (fun k => h ≫ φ k) j) :
    valAt' p _ ((LB.pullGen L φ ε c h).s j).val = valAt' (p ≫ h) _ (c.s j).val := by
  exact (vtf_val_res p _ hp _).trans (vtf_val_pullU _ _ _ _)
end ReciprocityTheory.ChartRestriction.G.PullbackSections
