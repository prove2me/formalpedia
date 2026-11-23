-- Prove2me | solution 1 for PI.GGConvScalarW.pi_sgn_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:33:55.645731+00:00
-- url     : https://prove2.me/submissions/8d9a627e-1693-4263-b250-34732e7b9c9a

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ScalarConvolutionTrace_CardUNeZero
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ScalarConvolutionTrace_SuperdiagSgnConj
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ScalarConvolutionTrace_AveragingOperatorIdempotent
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ScalarConvolutionTrace_IntertwinerRankLeOne
import Theorems.Thm_PI_GGConvScalarW_sgn_mul_self


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
open Classical
open PI PI.GGConvScalarW
open Formalism.L2.SG.GGMirabolic
variable {F : Type} [Field F] [Fintype F] {k : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
namespace PI.GGConvScalarW
theorem _root_.solution (π : Representation ℂ (GL (Fin k) F) V) (x : GL (Fin k) F) (v : V) :
    π (sgn k) (π x v) = π (sgn k * x * sgn k) (π (sgn k) v) := by
  rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul, mul_assoc (sgn k * x),
    sgn_mul_self, mul_one]
end PI.GGConvScalarW
