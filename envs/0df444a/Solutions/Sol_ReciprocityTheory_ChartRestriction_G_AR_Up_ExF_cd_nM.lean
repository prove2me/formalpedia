-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AR.Up.ExF.cd_nM
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T15:04:51.781175+00:00
-- url     : https://prove2.me/submissions/b6066c6f-2dc5-465d-98ac-2e6eba7ea24a

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_ExhaustFStatementPfC
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FourierCoefficientDomain
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_ExhaustStatementPfC
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_ExhaustFStatementPfD
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_LogPshAt_congr


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Up.ExF
open NumberField Complex Matrix Topology Filter ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst
  ReciprocityTheory.L2DbarEstimates ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Up.ExhA ReciprocityTheory.ChartRestriction.G.AR.Up.ExhB
  ReciprocityTheory.ChartRestriction.G.AR.Up.ExhC ReciprocityTheory.ChartRestriction.G.AR.Up.ExhD ReciprocityTheory.ChartRestriction.G.AR.Up.ExhE
open scoped ComplexConjugate ComplexOrder ContDiff
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.ExF
theorem _root_.solution (τ : X.Ψ) (a b : Fin r) : ContDiff ℂ ∞ fun z : V (nd X) => nM X z τ a b := by
  show ContDiff ℂ ∞ fun z : V (nd X) => nmat X z τ a b
  unfold nmat
  by_cases h : b < a
  · simp only [dif_pos h]
    first
      | exact (EuclideanSpace.proj (𝕜 := ℂ) _).contDiff
      | fun_prop
      | exact ((EuclideanSpace.proj (𝕜 := ℂ) _).contDiff).congr fun z => rfl
  · simp only [dif_neg h]
    exact contDiff_const
end ReciprocityTheory.ChartRestriction.G.AR.Up.ExF
