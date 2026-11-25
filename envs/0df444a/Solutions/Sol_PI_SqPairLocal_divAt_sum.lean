-- Prove2me | solution 1 for PI.SqPairLocal.divAt_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:28:43.409387+00:00
-- url     : https://prove2.me/submissions/41fd0d9e-dc25-4477-b142-80a045df4eff

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarePairLocal_SqPairLocalOfSteps
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarePairLocal_DivAtOneOfInt
import Theorems.Thm_PI_SqPairLocal_divAt_zero
import Theorems.Thm_PI_SqPairLocal_divAt_add

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField Matrix
open PI PI.SqPairLocal
open PI.SqPair Formalism.L2.PairingIndexBounds.Eq.SqG
variable {E : Type} [Field E] [NumberField E] [StarRing E]
variable {Q : Ideal (𝓞 E)} [hQ : Q.IsPrime]
namespace PI.SqPairLocal
theorem _root_.solution {c : 𝓞 E} {ι : Type} (S : Finset ι) (f : ι → E) (h : ∀ i ∈ S, DivAt Q c (f i)) :
    DivAt Q c (∑ i ∈ S, f i) :=
  Finset.sum_induction f (DivAt Q c) (fun _ _ ha hb => divAt_add ha hb) divAt_zero h
end PI.SqPairLocal
