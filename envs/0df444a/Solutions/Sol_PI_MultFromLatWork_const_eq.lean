-- Prove2me | solution 1 for PI.MultFromLatWork.const_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T09:57:30.952234+00:00
-- url     : https://prove2.me/submissions/42cc3ebe-69b6-4779-a3db-84b1eb33343a

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_LatCountG
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeMultiplicity_EncardLeOfFinset

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open scoped ENNReal
noncomputable section
open PI PI.MultFromLatWork
open Formalism.REAL
namespace PI.MultFromLatWork
theorem _root_.solution (I : Formalism.MainNotions.S.AutInst) (r : NumberField.InfinitePlace I.F → ℝ) (t : ℝ) :
    (3 * Real.sqrt (I.n : ℝ) / (t * t)) ^ (2 * I.n ^ 2 * I.f) *
        Real.exp (2 * (I.n : ℝ) ^ 2 * ∑ v, (2 * r v)) =
      PI.LatCountG.COm I r / t ^ (4 * I.n ^ 2 * I.f) := by
  have he : ∑ v, (2 * r v) = 2 * ∑ v, r v := by rw [Finset.mul_sum]
  have hp : t ^ (4 * I.n ^ 2 * I.f) = (t * t) ^ (2 * I.n ^ 2 * I.f) := by ring
  have hx : 2 * (I.n : ℝ) ^ 2 * (2 * ∑ v, r v) = 4 * (I.n : ℝ) ^ 2 * ∑ v, r v := by ring
  rw [PI.LatCountG.COm, hp, he, hx, div_pow]
  ring
end PI.MultFromLatWork
