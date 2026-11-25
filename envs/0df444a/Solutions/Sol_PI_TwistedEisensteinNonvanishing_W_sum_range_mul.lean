-- Prove2me | solution 1 for PI.TwistedEisensteinNonvanishing.W.sum_range_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:31:49.231333+00:00
-- url     : https://prove2.me/submissions/9962f671-ea3d-4c51-8935-a50e2315469e

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TwistedEisensteinCoset_IaDivDown
import Definitions.Def_Lemmata_PeriodicFunctions_PeriodicApplyMulAdd
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TwistedEisensteinCoset_WeightedSumScaling
import Theorems.Thm_Bl_PeriodicFunctions_goal1


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Module
noncomputable section
open PI PI.TwistedEisensteinNonvanishing PI.TwistedEisensteinNonvanishing.W
open Loc LocE
variable {K : Type} [Field K]
namespace PI.TwistedEisensteinNonvanishing.W
theorem _root_.solution (M m : ℕ) (g : ℕ → K) (hg : ∀ i, g (i + M) = g i) :
    ∑ i ∈ Finset.range (M * m), g i = (m : K) * ∑ i ∈ Finset.range M, g i := by
  first | exact Bl.PeriodicFunctions.goal1 .. | (apply Bl.PeriodicFunctions.goal1 <;> assumption) | (intros; apply Bl.PeriodicFunctions.goal1 <;> assumption)
end PI.TwistedEisensteinNonvanishing.W
