-- Prove2me | solution 1 for PlankProblem.sum_abs_le_card_of_norm_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T17:47:21.90242+00:00
-- url     : https://prove2.me/submissions/b6778b21-b9c8-4bd7-bd86-7eeb3029e812

module
public import Definitions.Def_BallPlank_ShiftedPlanks
public import Definitions.Def_BallPlank_BallPlankFinal

set_option autoImplicit true
@[expose] public section
public section
open Set
open scoped BigOperators InnerProductSpace Pointwise
noncomputable section
open PlankProblem
variable {n : ℕ}
local notation "Rn" => EuclideanSpace ℝ (Fin n)
namespace PlankProblem
theorem _root_.solution {ι : Type*} [Fintype ι] (z : EuclideanSpace ℝ ι)
    (hz : ‖z‖ ≤ Real.sqrt (Fintype.card ι)) : ∑ j, |z j| ≤ Fintype.card ι := by
  have h1 := sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := fun j => |z j|)
  have h2 : ‖z‖ ^ 2 = ∑ j, |z j| ^ 2 := by
    rw [EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)]
    simp
  have h3 : ‖z‖ ^ 2 ≤ Fintype.card ι := by
    calc ‖z‖ ^ 2 ≤ (Real.sqrt (Fintype.card ι)) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hz 2
      _ = Fintype.card ι := Real.sq_sqrt (Nat.cast_nonneg _)
  simp only [Finset.card_univ] at h1
  rw [← h2] at h1
  have h4 : (∑ j, |z j|) ^ 2 ≤ ((Fintype.card ι : ℕ) : ℝ) ^ 2 := by nlinarith
  exact (abs_le_of_sq_le_sq' h4 (Nat.cast_nonneg _)).2
end PlankProblem
