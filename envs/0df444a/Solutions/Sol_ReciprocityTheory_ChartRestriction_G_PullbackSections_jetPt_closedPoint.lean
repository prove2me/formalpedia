-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.PullbackSections.jetPt_closedPoint
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T16:12:23.191222+00:00
-- url     : https://prove2.me/submissions/7a2a3c3d-8f19-499d-95a8-78e7ae584eae

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_HolJetA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_TaylorMul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ValAtLem
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_FBIdJet
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_HolJetB
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_PullbackSections_jet__loc_e980629664a9
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_nbhdPt_closedPoint


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
open AlgebraicGeometry CategoryTheory Opposite Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.TB.ValAt
open scoped ContDiff
variable {g : ℕ} {Y : Scheme.{0}}
variable (e : (Fin g → ℂ) → (Sp ℂ ⟶ Y)) (hol : IsHolFam e)
namespace ReciprocityTheory.ChartRestriction.G.PullbackSections
theorem _root_.solution (m : ℕ) : jetPt e hol m (IsLocalRing.closedPoint _) = e 0 cpt :=
  nbhdPt_closedPoint _ _ (jetψ_loc e hol m)
end ReciprocityTheory.ChartRestriction.G.PullbackSections
