-- Prove2me | solution 1 for PI.SqPairLocal.stdHG_conj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:22:58.831372+00:00
-- url     : https://prove2.me/submissions/b32c66a3-7586-4468-82d3-ee9d620d1405

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarePairLocal_SqPairLocalOfSteps
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarePairLocal_IsMaximalComapCj

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
variable {E : Type} [Field E] [NumberField E] [StarRing E] {N : ℕ}
variable {L : Submodule (𝓞 E) (Fin N → E)}
namespace PI.SqPairLocal
theorem _root_.solution (e : Matrix (Fin N) (Fin N) E) (x y : Fin N → E) :
    stdHG E N x (eᴴ *ᵥ y) = stdHG E N (e *ᵥ x) y := by
  first
    | simp only [stdHG, Matrix.mulVec, dotProduct, Matrix.conjTranspose_apply, Finset.mul_sum,
        Finset.sum_mul, star_sum, star_mul']
    | simp only [stdHG, Matrix.mulVec, Matrix.dotProduct, Matrix.conjTranspose_apply,
        Finset.mul_sum, Finset.sum_mul, star_sum, star_mul']
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring
end PI.SqPairLocal
