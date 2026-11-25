-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.PullbackSections.vtf_val_res
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T15:09:39.546887+00:00
-- url     : https://prove2.me/submissions/477f553c-e462-4051-b0a3-996d7d4b4108

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_VtFrRdHol
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ThetaVV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_VtFrRdA

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
variable {Z Z' : Scheme.{0}}
namespace ReciprocityTheory.ChartRestriction.G.PullbackSections
theorem _root_.solution (p : Sp ℂ ⟶ Z) {U V : Z.Opens} (hVU : V ≤ U) (h : ⊤ ≤ p ⁻¹ᵁ V) (u : Γ(Z, U)ˣ) :
    valAt' p V (res hVU u : Γ(Z, V)) = valAt' p U (u : Γ(Z, U)) := by
  have h' : ⊤ ≤ p ⁻¹ᵁ U := h.trans (fun x hx => hVU hx)
  rw [valAt', valAt', dif_pos h, dif_pos h']
  delta valAt res
  congr 1
  first
  | (rw [Units.coe_map, MonoidHom.coe_coe, ← CommRingCat.comp_apply, Scheme.Hom.map_appLE])
  | simp [← CommRingCat.comp_apply, Scheme.Hom.map_appLE]
end ReciprocityTheory.ChartRestriction.G.PullbackSections
