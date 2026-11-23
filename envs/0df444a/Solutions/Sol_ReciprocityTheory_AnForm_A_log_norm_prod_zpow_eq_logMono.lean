-- Prove2me | solution 1 for ReciprocityTheory.AnForm.A.log_norm_prod_zpow_eq_logMono
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:02:17.098785+00:00
-- url     : https://prove2.me/submissions/a9306b7b-2425-4ca2-9616-fd77485cbffd

import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_LogIntSt
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_LogInt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Set
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A
namespace ReciprocityTheory.AnForm.A
theorem _root_.solution {D : ℕ} (m : Fin D → ℤ) (z : Fin D → ℂ)
    (hz : ∀ i, z i ≠ 0) : Real.log ‖∏ i, z i ^ m i‖ = logMono m z := by
  rw [norm_prod, Real.log_prod (fun i _ => norm_ne_zero_iff.mpr (zpow_ne_zero _ (hz i)))]
  unfold logMono
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [norm_zpow, Real.log_zpow]
end ReciprocityTheory.AnForm.A
