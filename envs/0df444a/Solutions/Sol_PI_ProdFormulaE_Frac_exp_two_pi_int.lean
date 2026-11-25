-- Prove2me | solution 1 for PI.ProdFormulaE.Frac.exp_two_pi_int
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:05:55.376366+00:00
-- url     : https://prove2.me/submissions/993f5d46-64dc-4161-886f-5e93fb1395c7

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProductFormulaHaar_DenEqOneOfForallPadicNormLeOne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open PI PI.ProdFormulaE PI.ProdFormulaE.Frac
namespace PI.ProdFormulaE.Frac
theorem _root_.solution (n : ℤ) : Complex.exp (2 * Real.pi * Complex.I * (n : ℂ)) = 1 := by
  rw [show 2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) = n * (2 * Real.pi * Complex.I) by ring]
  exact Complex.exp_int_mul_two_pi_mul_I n
end PI.ProdFormulaE.Frac
