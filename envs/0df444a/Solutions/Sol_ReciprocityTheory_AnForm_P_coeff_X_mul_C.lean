-- Prove2me | solution 1 for ReciprocityTheory.AnForm.P.coeff_X_mul_C
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:51:53.653306+00:00
-- url     : https://prove2.me/submissions/7ef0fd77-fbd1-4b80-a776-0b6985eb113b

import Definitions.Def_ReciprocityTheory_AnalyticForms_LeviForms_IsRegFamilyInhabitStatement
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_PshShiftA
import Definitions.Def_ReciprocityTheory_AnalyticForms_LeviForms_HomDensA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.P
open Filter Topology Polynomial Matrix
open scoped ContDiff
noncomputable section
namespace ReciprocityTheory.AnForm.P
theorem _root_.solution (a : ℂ) (n : ℕ) : (X * C a).coeff n = if n = 1 then a else 0 := by
  rw [mul_comm, Polynomial.coeff_C_mul_X]
end ReciprocityTheory.AnForm.P
