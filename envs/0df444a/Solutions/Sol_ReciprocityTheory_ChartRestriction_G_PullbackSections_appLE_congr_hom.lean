-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.PullbackSections.appLE_congr_hom
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T15:57:43.595059+00:00
-- url     : https://prove2.me/submissions/2eaa8c1a-5149-489a-b68e-c0b59509df26

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_HolJetE
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_HolJetF

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
variable {Y : Scheme.{0}}
variable {g : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.PullbackSections
theorem _root_.solution {A : CommRingCat.{0}} {q q' : Spec A ⟶ Y} (hq : q = q') (U : Y.Opens) (h : ⊤ ≤ q ⁻¹ᵁ U)
    (h' : ⊤ ≤ q' ⁻¹ᵁ U) : q.appLE U ⊤ h = q'.appLE U ⊤ h' := by
  subst hq
  rfl
end ReciprocityTheory.ChartRestriction.G.PullbackSections
