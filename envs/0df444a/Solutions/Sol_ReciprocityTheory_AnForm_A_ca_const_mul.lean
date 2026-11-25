-- Prove2me | solution 1 for ReciprocityTheory.AnForm.A.ca_const_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:05:41.406233+00:00
-- url     : https://prove2.me/submissions/4686914d-1fcb-4c4e-9171-5b9195e4afac

import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_IsPshLocallyIntegrableStatement
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshMollB
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshMoll

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A
open MeasureTheory Metric Filter Topology Set
noncomputable section
variable {D : ℕ}
namespace ReciprocityTheory.AnForm.A
theorem _root_.solution (c : ℝ) (f : ℂ → ℝ) :
    Real.circleAverage (fun ζ => c * f ζ) 0 1 = c * Real.circleAverage f 0 1 := by
  simp_rw [← smul_eq_mul]
  exact Real.circleAverage_fun_smul
end ReciprocityTheory.AnForm.A
