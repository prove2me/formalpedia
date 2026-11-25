-- Prove2me | solution 1 for PI.QnZeroLevelWork.quad_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:19:18.237703+00:00
-- url     : https://prove2.me/submissions/6eaf9630-ce49-454c-bfea-21198677f9d3

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ZeroLevelIndex_SecondMinorZeroLevelFormula
import Theorems.Thm_PI_QnZeroLevelWork_pair_sum

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
namespace PI.QnZeroLevelWork
theorem _root_.solution {M : Type*} [AddCommMonoid M] {n : ℕ}
    (T : Fin (n + 2) → Fin (n + 2) → Fin (n + 2) → Fin (n + 2) → M) :
    (∑ i : Fin (n + 2), ∑ i' : Fin (n + 2), ∑ j : Fin (n + 2), ∑ j' : Fin (n + 2),
      if i < i' ∧ j < j' then T i i' j j' else 0) =
    ∑ i : Fin (n + 2), ∑ i'' : Fin (n + 1), ∑ j : Fin (n + 2), ∑ j'' : Fin (n + 1),
      if (i : ℕ) ≤ (i'' : ℕ) ∧ (j : ℕ) ≤ (j'' : ℕ) then T i (i.succAbove i'') j (j.succAbove j'') else 0 := by
  refine sum_congr rfl fun i _ => ?_
  have h1 : ∀ i' : Fin (n + 2), (∑ j : Fin (n + 2), ∑ j' : Fin (n + 2),
      if i < i' ∧ j < j' then T i i' j j' else 0) =
      if i < i' then ∑ j : Fin (n + 2), ∑ j' : Fin (n + 2), (if j < j' then T i i' j j' else 0) else 0 := by
    intro i'; by_cases h : i < i' <;> simp [h]
  have h2 : ∀ i'' : Fin (n + 1), (∑ j : Fin (n + 2), ∑ j'' : Fin (n + 1),
      if (i : ℕ) ≤ (i'' : ℕ) ∧ (j : ℕ) ≤ (j'' : ℕ) then T i (i.succAbove i'') j (j.succAbove j'') else 0) =
      if (i : ℕ) ≤ (i'' : ℕ) then ∑ j : Fin (n + 2), ∑ j'' : Fin (n + 1),
        (if (j : ℕ) ≤ (j'' : ℕ) then T i (i.succAbove i'') j (j.succAbove j'') else 0) else 0 := by
    intro i''; by_cases h : (i : ℕ) ≤ (i'' : ℕ) <;> simp [h]
  simp only [h1, h2]
  rw [pair_sum i]
  refine sum_congr rfl fun i'' _ => ?_
  split_ifs
  · exact sum_congr rfl fun j _ => pair_sum j (fun j' => T i (i.succAbove i'') j j')
  · rfl
end PI.QnZeroLevelWork
