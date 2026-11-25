-- Prove2me | solution 1 for PI.AlgValsFin.W.factor_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T09:19:00.622948+00:00
-- url     : https://prove2.me/submissions/43802a0e-0f2b-4a2e-96d8-c87a4e3e8549

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AlgebraicValuesFinite_ClassSame
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AlgebraicValuesFinite_FactorOne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Formalism.L2.Host Neutral.B1
open PI PI.AlgValsFin PI.AlgValsFin.W
variable {L : Type} [Field L] [NumberField L]
namespace PI.AlgValsFin.W
theorem _root_.solution (N : ℝ) (hN : 0 < N) (o : ℤ) (s : ℝ) : (N ^ o) ^ s * (N ^ (-s)) ^ o = 1 := by
  have h1 : (N ^ o) ^ s = N ^ ((o : ℝ) * s) := by
    rw [← Real.rpow_intCast, ← Real.rpow_mul hN.le]
  have h2 : (N ^ (-s)) ^ o = N ^ (-s * (o : ℝ)) := by
    rw [← Real.rpow_intCast, ← Real.rpow_mul hN.le]
  have h3 : (o : ℝ) * s + -s * (o : ℝ) = 0 := by ring
  rw [h1, h2, ← Real.rpow_add hN, h3, Real.rpow_zero]
end PI.AlgValsFin.W
