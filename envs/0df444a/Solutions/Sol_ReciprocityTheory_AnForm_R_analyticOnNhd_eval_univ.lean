-- Prove2me | solution 1 for ReciprocityTheory.AnForm.R.analyticOnNhd_eval_univ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:08:24.045321+00:00
-- url     : https://prove2.me/submissions/4d44f0bb-c1c0-4897-83c7-bb0c7f657622

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_JacChart
import Definitions.Def_ReciprocityTheory_AnalyticForms_AnalyticCharts_ExistsAnalyticGraphChartMvPolynomial
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_AnChartA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.R
open MvPolynomial
noncomputable section
variable {n : ℕ}
namespace ReciprocityTheory.AnForm.R
theorem _root_.solution (q : MvPolynomial (Fin n) ℂ) :
    AnalyticOnNhd ℂ (fun y : Fin n → ℂ => eval y q) Set.univ := by
  exact AnalyticOnNhd.eval_mvPolynomial q
end ReciprocityTheory.AnForm.R
