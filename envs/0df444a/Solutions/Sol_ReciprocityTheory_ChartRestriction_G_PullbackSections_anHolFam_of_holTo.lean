-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.PullbackSections.anHolFam_of_holTo
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:48:16.415081+00:00
-- url     : https://prove2.me/submissions/948382c7-132f-4d41-b721-29bcab41215a

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_HolJetE
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ThGerm
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_AnHolFamOfHolTo

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
open AlgebraicGeometry CategoryTheory Limits Opposite MonoidalCategory CartesianMonoidalCategory MonObj
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.TB.ValAt
open scoped ContDiff
attribute [local instance] Over.cartesianMonoidalCategory
variable {Y : Scheme.{0}}
namespace ReciprocityTheory.ChartRestriction.G.PullbackSections
theorem _root_.solution {N : ℕ} {y : (Fin N → ℂ) → (Sp ℂ ⟶ Y)} (h : IsHolTo Set.univ y) : IsHolFam y := by
  intro U f
  obtain ⟨h1, h2⟩ := h U f
  simp only [Set.mem_univ, true_and] at h1 h2
  exact ⟨h1, h2⟩
end ReciprocityTheory.ChartRestriction.G.PullbackSections
