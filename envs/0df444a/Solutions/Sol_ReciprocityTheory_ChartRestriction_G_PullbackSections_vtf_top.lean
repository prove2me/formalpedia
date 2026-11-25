-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.PullbackSections.vtf_top
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T15:15:07.150244+00:00
-- url     : https://prove2.me/submissions/34638344-18cc-4a3a-bf53-a5b6854baaf9

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_HolJetC
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_VtFrRdHol

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
open AlgebraicGeometry CategoryTheory Limits Opposite Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.TB.ValAt
namespace ReciprocityTheory.ChartRestriction.G.PullbackSections
theorem _root_.solution {Z : Scheme.{0}} (x : Sp ℂ ⟶ Z) : ⊤ ≤ x ⁻¹ᵁ (⊤ : Z.Opens) := le_top
end ReciprocityTheory.ChartRestriction.G.PullbackSections
