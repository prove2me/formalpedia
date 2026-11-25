-- Prove2me | solution 1 for ReciprocityTheory.AnForm.P.coeff_X_pow_mul_C
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:07:03.435619+00:00
-- url     : https://prove2.me/submissions/e5615b78-fc85-42ce-8920-ef9b6cdaa6f5

import Definitions.Def_ReciprocityTheory_AnalyticForms_LeviForms_HomDensA
import Definitions.Def_ReciprocityTheory_AnalyticForms_LeviForms_HomDensB

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.P
open Polynomial Matrix
noncomputable section
namespace ReciprocityTheory.AnForm.P
theorem _root_.solution (a : ℂ) (k n : ℕ) : (X ^ k * C a).coeff n = if n = k then a else 0 := by
  rw [mul_comm, coeff_C_mul_X_pow]
end ReciprocityTheory.AnForm.P
