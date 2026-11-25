-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AR.Up.PairUnfoldPf.ka_meas
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:35:42.145931+00:00
-- url     : https://prove2.me/submissions/b5b8c05c-9fb8-4f3b-aca4-c0605cdf0741

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_PairUnfoldPfB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_PairUnfoldPf
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_ExtFPf_cont_dmin
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_PairUnfoldPf_cpt_cont


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Up.PairUnfoldPf
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ENNReal Matrix
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.PairUnfoldPf
theorem _root_.solution (x0 : Frame X.Ψ r) (bb : ℝ) : Measurable (kaF X x0 bb) := by
  have hd : ∀ τ : X.Ψ, Measurable fun z => dmin X.Gm (cpt X x0 z) τ ⟨X.p0, Nat.lt_succ_of_le X.p0_le⟩ :=
    fun τ => ((ExtFPf.cont_dmin X τ _).comp (cpt_cont X x0)).measurable
  unfold kaF rhF
  exact Real.measurable_exp.comp (measurable_const.mul
    (Finset.measurable_sum _ fun τ _ => Real.measurable_log.comp (hd τ).norm).neg)
end ReciprocityTheory.ChartRestriction.G.AR.Up.PairUnfoldPf
