-- Prove2me | solution 1 for ReciprocityTheory.AnForm.A.kK_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:06:14.369809+00:00
-- url     : https://prove2.me/submissions/4cecc12c-d00c-42bf-88d0-0d186d02a91a

import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_IsPshLocallyIntegrableStatement
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_ContinuousTmaxShift
import Theorems.Thm_P2M_ReciprocityTheory_AnForm_A_k__nonneg_95fdb6d5ed2b

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A
open MeasureTheory Metric Filter Topology
open scoped ContDiff Interval
noncomputable section
variable {ι : Type*} [Fintype ι]
namespace ReciprocityTheory.AnForm.A
theorem _root_.solution (h : ι → ℝ) : 0 ≤ kK h := Finset.prod_nonneg fun j _ => kθ_nonneg _
end ReciprocityTheory.AnForm.A
