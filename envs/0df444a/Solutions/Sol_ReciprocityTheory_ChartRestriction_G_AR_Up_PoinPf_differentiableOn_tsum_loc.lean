-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AR.Up.PoinPf.differentiableOn_tsum_loc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T13:02:49.13867+00:00
-- url     : https://prove2.me/submissions/2fc7f389-d93b-4fdd-a8c9-b5d3a1f261b6

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_FundSetMeasStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_PairUnfoldPfA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_OrthogonalFrameDomain
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FourierCoefficientDomain
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_OrthonormalFlagTranslateHolds
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Calculus.SmoothSeries
import Definitions.Def_Lemmata_GeneralBFactVersion_Imports
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_PoinStatementPfA
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_PoinPf_fderiv_bound_ball

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Up.PoinPf
open Metric
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.PoinPf
theorem _root_.solution {ι Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℂ Y] {U : Set Y}
    (hU : IsOpen U) (f : ι → Y → ℂ) (hf : ∀ i, DifferentiableOn ℂ (f i) U)
    (hb : ∀ y ∈ U, ∃ ε > 0, ∃ u : ι → ℝ, Summable u ∧ ∀ i, ∀ v ∈ ball y ε, ‖f i v‖ ≤ u i) :
    DifferentiableOn ℂ (fun y => ∑' i, f i y) U := by
  intro y0 hy0
  obtain ⟨ε, hε, u, hu, hub⟩ := hb y0 hy0
  obtain ⟨δ, hδ, hδU⟩ := isOpen_iff.1 hU y0 hy0
  set m := min ε δ with hm
  have hm0 : 0 < m := lt_min hε hδ
  set R := m / 4 with hR
  have hR0 : 0 < R := by positivity
  have hsub : ∀ y ∈ ball y0 R, ball y (2 * R) ⊆ ball y0 m := by
    intro y hy v hv
    rw [mem_ball] at *
    calc dist v y0 ≤ dist v y + dist y y0 := dist_triangle _ _ _
      _ < 2 * R + R := add_lt_add hv hy
      _ ≤ m := by rw [hR]; linarith
  have hε' : ball y0 m ⊆ ball y0 ε := ball_subset_ball (min_le_left _ _)
  have hδ' : ball y0 m ⊆ U := (ball_subset_ball (min_le_right _ _)).trans hδU
  have hin : ∀ y ∈ ball y0 R, y ∈ U := fun y hy => hδ' (hsub y hy (mem_ball_self (by linarith)))
  have hder : ∀ i, ∀ y ∈ ball y0 R, HasFDerivAt (f i) (fderiv ℂ (f i) y) y := fun i y hy =>
    ((hf i y (hin y hy)).differentiableAt (hU.mem_nhds (hin y hy))).hasFDerivAt
  have hbd : ∀ i, ∀ y ∈ ball y0 R, ‖fderiv ℂ (f i) y‖ ≤ u i / R := fun i y hy =>
    fderiv_bound_ball hR0 ((hf i).mono ((hsub y hy).trans hδ')) (fun v hv => hub i v (hε' (hsub y hy hv)))
  have hs := hasFDerivAt_tsum_of_isPreconnected (hu.div_const R) isOpen_ball
    (convex_ball y0 R).isPreconnected hder hbd (mem_ball_self hR0)
    (Summable.of_norm_bounded hu fun i => hub i y0 (mem_ball_self hε)) (mem_ball_self hR0)
  exact hs.differentiableAt.differentiableWithinAt
end ReciprocityTheory.ChartRestriction.G.AR.Up.PoinPf
