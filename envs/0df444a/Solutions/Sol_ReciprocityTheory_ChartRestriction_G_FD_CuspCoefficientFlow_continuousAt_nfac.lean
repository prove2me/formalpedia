-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.CuspCoefficientFlow.continuousAt_nfac
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:52:12.141957+00:00
-- url     : https://prove2.me/submissions/87769444-5dd1-448f-abd4-f73af47a409f

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FourierCoefficientDomain
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FlowCoefficientBounds
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_CuspCoefficientFlow
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_CuspCoefficientFlow_cont_dmin
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_FlowCoefficientBounds_dmin_ne


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.CuspCoefficientFlow
open NumberField Complex ReciprocityTheory.ChartRestriction.G.FD MeasureTheory Metric Set Filter
open scoped ComplexConjugate Topology
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
namespace ReciprocityTheory.ChartRestriction.G.FD.CuspCoefficientFlow
theorem _root_.solution (la : Wt X.Ψ r) {x0 : Frame X.Ψ r} (hx0 : x0 ∈ X.dom) :
    ContinuousAt (X.nfac la) x0 := by
  have h : ∀ (τ : X.Ψ) (i : Fin r), ContinuousAt (fun x : Frame X.Ψ r =>
      ‖dmin X.Gm x τ i.succ / dmin X.Gm x τ i.castSucc‖ ^ (-(la τ i : ℝ) / 2)) x0 := by
    intro τ i
    have hd1 := (cont_dmin X τ i.succ).continuousAt (x := x0)
    have hd2 := (cont_dmin X τ i.castSucc).continuousAt (x := x0)
    have hne1 := FlowCoefficientBounds.dmin_ne X hx0 τ i.succ
    have hne2 := FlowCoefficientBounds.dmin_ne X hx0 τ i.castSucc
    exact (hd1.div hd2 hne2).norm.rpow_const (Or.inl (norm_ne_zero_iff.mpr (div_ne_zero hne1 hne2)))
  unfold Data.nfac
  exact tendsto_finset_prod _ fun τ _ => tendsto_finset_prod _ fun i _ => h τ i
end ReciprocityTheory.ChartRestriction.G.FD.CuspCoefficientFlow
