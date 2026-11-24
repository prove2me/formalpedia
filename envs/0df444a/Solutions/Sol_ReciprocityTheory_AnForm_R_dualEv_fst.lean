-- Prove2me | solution 1 for ReciprocityTheory.AnForm.R.dualEv_fst
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:36:52.958386+00:00
-- url     : https://prove2.me/submissions/79b56bcd-09f4-4739-81d2-fe7818d5c8ff

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_JacChart
import Definitions.Def_ReciprocityTheory_AnalyticForms_AnalyticCharts_ExistsAnalyticGraphChartMvPolynomial
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_AnChartA
import Theorems.Thm_ReciprocityTheory_AnForm_R_dualEv_fst_snd

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
theorem _root_.solution (p v : Fin n → ℂ) (h : MvPolynomial (Fin n) ℂ) :
    (dualEv p v h).fst = eval p h := (dualEv_fst_snd p v h).1
end ReciprocityTheory.AnForm.R
