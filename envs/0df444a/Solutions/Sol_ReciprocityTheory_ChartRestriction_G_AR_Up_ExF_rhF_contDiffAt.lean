-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AR.Up.ExF.rhF_contDiffAt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T16:31:06.80816+00:00
-- url     : https://prove2.me/submissions/022dd9e6-6165-4b76-ad27-a222445e9da6

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_ExhaustFStatementPfC
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FourierCoefficientDomain
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_ExhaustStatementPfC
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_ExhaustFStatementPfD
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_ExF_cd_detAm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_ExF_mem_OmF_iff
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_ExF_rhF_eq_sum
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_CkR_comp
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_SmoothR_comp


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
theorem _root_.solution (x0 : Frame X.Ψ r) (ho : IsOrth X x0) {z : V (nd X)} (hz : z ∈ OmF X x0) : ContDiffAt ℝ ∞ (rhF X x0) z := by
  have hfun : rhF X x0 = fun w => -∑ τ, Real.log ‖(Am X w τ).det‖ := funext (rhF_eq_sum X x0 ho)
  have hpd := (mem_OmF_iff X x0 ho z).1 hz
  rw [hfun]
  refine (ContDiffAt.sum fun τ _ => ?_).neg
  have hne : (Am X z τ).det ≠ 0 := (hpd τ).det_pos.ne'
  have h1 : ContDiffAt ℝ ∞ (fun w : V (nd X) => (Am X w τ).det) z := (cd_detAm X τ).contDiffAt
  have h2 : ContDiffAt ℝ ∞ (fun w : V (nd X) => ‖(Am X w τ).det‖) z :=
    (contDiffAt_norm ℂ hne).comp z h1
  exact h2.log (norm_ne_zero_iff.2 hne)
end ReciprocityTheory.ChartRestriction.G.AR.Up.ExF
