-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AR.Up.OntoB.cd_dmin
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:55:16.089984+00:00
-- url     : https://prove2.me/submissions/eeea20dd-78d2-442f-996f-74eaeae96f70

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_FundSetMeasStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_ExhaustStatementPfB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FourierCoefficientDomain
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_EventuallyDifferentiableAtOfContDiffAt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_OntoStatementPfB
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_OntoB_cd_cpt_entry

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Up.OntoB
open NumberField Complex Matrix Topology Filter ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst
  ReciprocityTheory.L2DbarEstimates ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Up.ExhC ReciprocityTheory.ChartRestriction.G.AR.Up.ExhD
open scoped ComplexConjugate ContDiff
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r) (x0 : Frame X.Ψ r)
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.OntoB
theorem _root_.solution (τ : X.Ψ) (i : Fin (r + 1)) :
    ContDiff ℝ ∞ fun z : V (nd X) => dmin X.Gm (cpt X x0 z) τ i := by
  have hE : ∀ (τ : X.Ψ) (a b : Fin r), ContDiff ℝ ∞ fun z : V (nd X) => cpt X x0 z τ a b :=
    fun τ a b => (cd_cpt_entry X x0 τ a b).restrict_scalars ℝ
  have hC : ∀ (τ : X.Ψ) (a b : Fin r),
      ContDiff ℝ ∞ fun z : V (nd X) => starRingEnd ℂ (cpt X x0 z τ a b) := by
    intro τ a b
    have h := Complex.conjCLE.contDiff.comp (hE τ a b)
    simpa [Function.comp_def] using h
  unfold dmin lminor
  simp only [Matrix.det_apply, Units.smul_def, zsmul_eq_mul]
  refine ContDiff.sum fun σ _ => contDiff_const.mul ?_
  refine contDiff_prod fun k _ => ?_
  simp only [Matrix.submatrix_apply, ReciprocityTheory.ChartRestriction.G.FD.gram, ReciprocityTheory.ChartRestriction.G.FD.hermC,
      ReciprocityTheory.ChartRestriction.G.FD.col, ReciprocityTheory.ChartRestriction.G.FD.mat, Matrix.of_apply]
  refine ContDiff.sum fun c _ => ContDiff.sum fun d _ => ?_
  exact ((hE τ c _).mul contDiff_const).mul (hC τ d _)
end ReciprocityTheory.ChartRestriction.G.AR.Up.OntoB
