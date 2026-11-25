-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.FourierCoefficientDomain.norm_fderiv_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:54:42.64713+00:00
-- url     : https://prove2.me/submissions/2e3f405e-d5db-4c9e-a1fc-b53601fd0896

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FourierCoefficientMatrices
import Definitions.Def_Lemmata_GeneralBFactBisForm_Imports
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FourierCoefficientDomain
import Theorems.Thm_Bl_general_b_fact_bis_form_goal1


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.FourierCoefficientDomain
open NumberField Complex ReciprocityTheory.ChartRestriction.G.FD MeasureTheory Metric Set Filter
open scoped ComplexConjugate Topology
noncomputable section
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
namespace ReciprocityTheory.ChartRestriction.G.FD.FourierCoefficientDomain
theorem _root_.solution {U : Set F} (hU : IsOpen U) {G : F → ℂ} (hG : DifferentiableOn ℂ G U)
    {y : F} {R C : ℝ} (hR : 0 < R) (hball : closedBall y R ⊆ U)
    (hC : ∀ z ∈ closedBall y R, ‖G z‖ ≤ C) : ‖fderiv ℂ G y‖ ≤ C / R := by
  first | exact Bl.general_b_fact_bis_form.goal1 .. | (apply Bl.general_b_fact_bis_form.goal1 <;> assumption) | (intros; apply Bl.general_b_fact_bis_form.goal1 <;> assumption)
end ReciprocityTheory.ChartRestriction.G.FD.FourierCoefficientDomain
