-- Prove2me | solution 1 for SeqDiagnosis.BeliefRecon.etm_list_prod
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-20T09:57:32.025835+00:00
-- url     : https://prove2.me/submissions/677017ac-6976-4d75-aa01-db31cde4e57a

import Mathlib
import Definitions.Def_SeqDiagnosis_BeliefRecon_Model

open Matrix SeqDiagnosis.BeliefRecon

theorem solution {Y : Type*} [MeasurableSpace Y] {N p : ℕ}
    (M : Model Y N p) (hS : M.Standing) (hETM : M.ETM)
    (j : Fin N) (ys : List Y) :
    (ys.map (M.f j.succ)).prod = (ys.map (M.f 0)).prod *
      Real.exp ((ys.length : ℝ) * M.normConst (M.beta j) + M.beta j ⬝ᵥ (ys.map M.h).sum) := by
  induction ys with
  | nil => simp
  | cons y ys ih =>
    simp only [List.map_cons, List.prod_cons, List.sum_cons, List.length_cons, ih, hETM j y,
      dotProduct_add, Nat.cast_succ]
    simp only [add_mul, one_mul, Real.exp_add]
    ring
