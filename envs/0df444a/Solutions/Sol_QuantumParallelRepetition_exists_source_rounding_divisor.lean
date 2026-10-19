-- Prove2me | solution 1 for QuantumParallelRepetition.exists_source_rounding_divisor
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:15.858309+00:00
-- url     : https://prove2.me/submissions/33aab99e-d7bc-4cb6-aa0e-6c2f917d1fc5

import Mathlib
import Definitions.Def_QuantumParallelRepetition
import Theorems.Thm_QuantumParallelRepetition_sourceAnswerAlphabetBound_log_nonneg

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open QuantumParallelRepetition
open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset
noncomputable section
open scoped BigOperators InnerProductSpace
variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
namespace QuantumParallelRepetition
theorem _root_.solution
    (A B : Type*) [Fintype A] [Fintype B]
    {K η δ : ℝ}
    (hK : 0 ≤ K) (hη : 0 < η) (hδ : 0 < δ) :
    ∃ q : ℕ, 2 ≤ q ∧
      8 * K *
          ((2 * Real.log (sourceAnswerAlphabetBound A B) + η / 2) /
            (q : ℝ)) ≤
        δ ^ 2 := by
  let C : ℝ :=
    8 * K * (2 * Real.log (sourceAnswerAlphabetBound A B) + η / 2)
  have hC : 0 ≤ C := by
    dsimp [C]
    have hlog := sourceAnswerAlphabetBound_log_nonneg A B
    positivity
  have hsquare : 0 < δ ^ 2 := sq_pos_of_pos hδ
  obtain ⟨q, hq⟩ := exists_nat_gt
    (max (2 : ℝ) (C / δ ^ 2))
  have htwo : (2 : ℝ) < (q : ℝ) :=
    lt_of_le_of_lt (le_max_left _ _) hq
  have hqnat : 2 ≤ q := by
    have hstrict : 2 < q := by exact_mod_cast htwo
    omega
  have hqreal : 0 < (q : ℝ) := by positivity
  have hthreshold : C / δ ^ 2 < (q : ℝ) :=
    lt_of_le_of_lt (le_max_right _ _) hq
  have hsmall : C / (q : ℝ) < δ ^ 2 := by
    apply (div_lt_iff₀ hqreal).mpr
    have hcross := (div_lt_iff₀ hsquare).mp hthreshold
    nlinarith [hC]
  refine ⟨q, hqnat, ?_⟩
  calc
    8 * K *
        ((2 * Real.log (sourceAnswerAlphabetBound A B) + η / 2) /
          (q : ℝ)) = C / (q : ℝ) := by
      dsimp [C]
      ring
    _ ≤ δ ^ 2 := hsmall.le
end QuantumParallelRepetition
