-- Prove2me | solution 1 for PIW.FdPA.div_le_exp_of_abs_log_sub_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T11:23:50.816682+00:00
-- url     : https://prove2.me/submissions/afc55d2a-05d1-4db6-94f8-fa08c639fe66

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainExtension_PointAssembly_ZnNonneg
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainExtension_PointAssembly_DivLeExpOfAbsLogSubLe

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PIW PIW.FdPA
open ReciprocityTheory.ChartRestriction.G.FD NumberField Complex Metric
noncomputable section
namespace PIW.FdPA
theorem _root_.solution {a b K : ℝ} (ha : 0 < a) (hb : 0 < b) (h : |Real.log b - Real.log a| ≤ K) :
    a / b ≤ Real.exp K := by
  have h1 : a / b = Real.exp (Real.log a - Real.log b) := by
    rw [Real.exp_sub, Real.exp_log ha, Real.exp_log hb]
  rw [h1]
  apply Real.exp_le_exp.mpr
  have h2 := neg_le_abs (Real.log b - Real.log a)
  linarith
end PIW.FdPA
