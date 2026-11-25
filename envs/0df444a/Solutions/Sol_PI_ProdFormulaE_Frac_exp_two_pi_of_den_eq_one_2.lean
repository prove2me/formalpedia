-- Prove2me | solution 2 for PI.ProdFormulaE.Frac.exp_two_pi_of_den_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:12:03.742035+00:00
-- url     : https://prove2.me/submissions/4ae54f8e-3864-4dc4-8307-42810e02ab17

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProductFormulaHaar_DenEqOneOfForallPadicNormLeOne
import Theorems.Thm_PI_ProdFormulaE_Frac_exp_two_pi_int

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
theorem _root_.solution {a : ℚ} (ha : a.den = 1) :
    Complex.exp (2 * Real.pi * Complex.I * (a : ℂ)) = 1 := by
  have h : (a : ℂ) = ((a.num : ℤ) : ℂ) := by
    calc (a : ℂ) = (((a.num : ℤ) : ℚ) : ℂ) :=
          congrArg (fun x : ℚ => (x : ℂ)) (Rat.coe_int_num_of_den_eq_one ha).symm
      _ = ((a.num : ℤ) : ℂ) := Rat.cast_intCast _
  rw [h]
  exact exp_two_pi_int _
end PI.ProdFormulaE.Frac
