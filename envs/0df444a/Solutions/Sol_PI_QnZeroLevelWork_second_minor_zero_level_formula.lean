-- Prove2me | solution 1 for PI.QnZeroLevelWork.second_minor_zero_level_formula
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:27:37.886612+00:00
-- url     : https://prove2.me/submissions/659b219a-c099-4ff0-ba5d-1c3884a8b5f6

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ZeroLevelIndex_SecondMinorZeroLevelFormula
import Theorems.Thm_PI_QnZeroLevelWork_quad_sum
import Theorems.Thm_PI_QnZeroLevelWork_qm_congr
import Theorems.Thm_PI_QnZeroLevelWork_comp2

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
noncomputable section
open PI PI.QnZeroLevelWork
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {k r : ℕ}
namespace PI.QnZeroLevelWork
theorem _root_.solution (u : ℂ) (a a' β β' : Mx (k + 1) r → Fin (2 * r + k + 2) → ℂ) (f : Mx (k + 1) r → E) :
    chat2L (EH (k + 1) r) (posL (k + 1) r 0) u a a' β β' f =
      chat2Op (m := 2 * r + k) (EabH (Hpk (k + 1) r)) u a a' β β' f := by
  funext g
  calc chat2L (EH (k + 1) r) (posL (k + 1) r 0) u a a' β β' f g
      = ∑ i : Fin (2 * r + k + 2), ∑ i' : Fin (2 * r + k + 2), ∑ j : Fin (2 * r + k + 2),
          ∑ j' : Fin (2 * r + k + 2),
          (if i < i' ∧ j < j' then T2 u a a' β β' f g i i' j j' else 0) := rfl
    _ = ∑ i : Fin (2 * r + k + 2), ∑ i'' : Fin (2 * r + k + 1), ∑ j : Fin (2 * r + k + 2),
          ∑ j'' : Fin (2 * r + k + 1),
          (if (i : ℕ) ≤ (i'' : ℕ) ∧ (j : ℕ) ≤ (j'' : ℕ) then
            T2 u a a' β β' f g i (i.succAbove i'') j (j.succAbove j'') else 0) := quad_sum _
    _ = chat2Op (m := 2 * r + k) (EabH (Hpk (k + 1) r)) u a a' β β' f g := by
      unfold chat2Op minor2Op
      refine sum_congr rfl fun i _ => sum_congr rfl fun i'' _ => sum_congr rfl fun j _ =>
        sum_congr rfl fun j'' _ => ?_
      split_ifs with h
      · exact congrArg (((-1 : ℂ) ^ ((i : ℕ) + (i.succAbove i'' : ℕ) + (j : ℕ) + (j.succAbove j'' : ℕ)) *
            (β g i * β' g (i.succAbove i'') - β g (i.succAbove i'') * β' g i) *
            (a g j * a' g (j.succAbove j'') - a g (j.succAbove j'') * a' g j)) • ·)
          (congrFun (qm_congr (EH (k + 1) r) _ _ _ _ (comp2 i i'' h.1) (comp2 j j'' h.2) u f) g)
      · rfl
end PI.QnZeroLevelWork
