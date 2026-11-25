-- Prove2me | solution 1 for ReciprocityTheory.AnForm.A.mixedCof_one_diag
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:30:18.132897+00:00
-- url     : https://prove2.me/submissions/2ed2cc40-9bdb-4c88-bade-c4cb52c04b9a

import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_ContDiffOfContDiffOnZeroOff
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_LogInt
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_GreenCoord
import Definitions.Def_ReciprocityTheory_AnalyticForms_AnalyticCharts_Osgood
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_HasCompactSupportCompHypInclAt
import Theorems.Thm_ReciprocityTheory_AnForm_A_mdisc_const
import Theorems.Thm_ReciprocityTheory_AnForm_A_mixedCof_diag


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A
open MeasureTheory Filter Topology
open scoped ContDiff
noncomputable section
variable {n : ℕ}
namespace ReciprocityTheory.AnForm.A
theorem _root_.solution (i : Fin (n + 1)) :
    mixedCof (fun _ : Fin n => (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)) i i =
      ((1 / ((n : ℝ) + 1) : ℝ) : ℂ) := by
  rw [mixedCof_diag]
  have h1 : (fun _ : Fin n => ((1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)).submatrix i.succAbove i.succAbove) =
      fun _ => (1 : Matrix (Fin n) (Fin n) ℂ) := by
    funext _
    exact Matrix.submatrix_one _ Fin.succAbove_right_injective
  rw [h1, mdisc_const, Matrix.det_one, mul_one]
  push_cast
  ring
end ReciprocityTheory.AnForm.A
