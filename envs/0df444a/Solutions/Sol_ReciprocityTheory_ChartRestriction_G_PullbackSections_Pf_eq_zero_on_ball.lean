-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.eq_zero_on_ball
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T13:27:32.215438+00:00
-- url     : https://prove2.me/submissions/9e89ad04-23ad-4996-a7ca-5169ba8f9a1e

import Mathlib
import Definitions.Def_Lemmata_FirstBlockLemmaJ_Imports
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_EqZeroOfMulEqZero
import Theorems.Thm_Bl_FirstBlockLemmaJ_goal1


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.PullbackSections ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf
open Metric Set Filter Topology
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
namespace ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf
theorem _root_.solution {g : V → ℂ} {x : V} {ε : ℝ} (hg : DifferentiableOn ℂ g (ball x ε)) {z : V}
    (hz : z ∈ ball x ε) (hgz : g =ᶠ[𝓝 z] 0) : ∀ y ∈ ball x ε, g y = 0 := by
  first | exact Bl.FirstBlockLemmaJ.goal1 .. | (apply Bl.FirstBlockLemmaJ.goal1 <;> assumption) | (intros; apply Bl.FirstBlockLemmaJ.goal1 <;> assumption)
end ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf
