-- Prove2me | solution 1 for ReciprocityTheory.AnForm.P.star_mul_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:07:44.286647+00:00
-- url     : https://prove2.me/submissions/43275c22-7cec-43eb-8fd4-2eb1bb0172d7

import Definitions.Def_ReciprocityTheory_AnalyticForms_LeviForms_IsRegFamilyInhabitStatement
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_PshShiftA
import Definitions.Def_ReciprocityTheory_AnalyticForms_LeviForms_HomDensB
import Definitions.Def_ReciprocityTheory_AnalyticForms_LeviForms_HomDens

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.P
open MeasureTheory
noncomputable section
open Matrix Polynomial
namespace ReciprocityTheory.AnForm.P
theorem _root_.solution (h : ℝ) (z : ℂ) : star z * ((h : ℂ) * z) = ((h * ‖z‖ ^ 2 : ℝ) : ℂ) := by
  rw [Complex.ofReal_mul, ← Complex.normSq_eq_norm_sq, Complex.normSq_eq_conj_mul_self]
  change (starRingEnd ℂ) z * _ = _
  ring
end ReciprocityTheory.AnForm.P
