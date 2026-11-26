-- Prove2me | solution 1 for ReciprocityTheory.AnForm.A.one_le_inf
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-26T03:37:18.24727+00:00
-- url     : https://prove2.me/submissions/90950c58-d775-49aa-bed2-cf83548be75c

import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_ContinuousTmaxShift
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshRegMax
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
variable {ι : Type*} [Fintype ι] [Nonempty ι]
theorem _root_.solution : (1 : WithTop ℕ∞) ≤ ∞ := by
  first
    | (exact_mod_cast (le_top : ((1 : ℕ∞) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞)))
    | (exact WithTop.coe_le_coe.2 le_top)
    | (decide)
    | (exact_mod_cast le_top)

