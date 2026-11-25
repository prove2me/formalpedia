-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.ClassNumImQInt.intBasis
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:52:49.941948+00:00
-- url     : https://prove2.me/submissions/c98261a3-09dd-4bab-880e-e006cb798cf6

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_ClassNumImQ
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuadraticDifference_QuadraticDifferenceForm
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ClassNumberIntegrality_HalfIntegral
import Theorems.Thm_PI_UnitaryGroupMassFormula_ClassNumImQInt_adjoin_top
import Theorems.Thm_PI_UnitaryGroupMassFormula_ClassNumImQInt_half_integral
import Theorems.Thm_PI_QD_quadraticDifferenceArith
import Theorems.Thm_PI_QD_quadratic_difference_form
import Theorems.Thm_PI_QD_quadratic_intCoeffs


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.ClassNumImQInt
open NumberField Polynomial
namespace PI.UnitaryGroupMassFormula.ClassNumImQInt
theorem _root_.solution : PI.ClassNumImQ.IntBasis := by
  intro d K _ _ b ⟨hp, hd, _, hb, htop⟩
  have hsq : Squarefree d := hp.prime.squarefree
  have htop' := adjoin_top b htop
  refine ⟨half_integral d b hd hb, ?_⟩
  intro z
  obtain ⟨x, y, hxy⟩ := PI.QD.quadratic_difference_form K d b hb htop' (z : K)
  have hint : IsIntegral ℤ ((x : K) + (y : K) * b) := by rw [← hxy]; exact z.isIntegral_coe
  obtain ⟨h2x, hN⟩ := PI.QD.quadratic_intCoeffs K d b x y hsq hd hb hint
  obtain ⟨a, v, hx, hy⟩ := PI.QD.quadraticDifferenceArith d x y hsq hd h2x hN
  refine ⟨a, v, ?_⟩
  rw [hxy, hx, hy]
  push_cast
  ring
end PI.UnitaryGroupMassFormula.ClassNumImQInt
