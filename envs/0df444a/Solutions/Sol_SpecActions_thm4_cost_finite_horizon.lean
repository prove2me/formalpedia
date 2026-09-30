-- Prove2me | solution 1 for SpecActions.thm4_cost_finite_horizon
-- status  : ACCEPTED   (prove)
-- author  : @Hartmann_Psi
-- created : 2026-09-12T04:19:01.137646+00:00
-- url     : https://prove2.me/submissions/0a199724-83e3-47e7-95d2-cc13e645f123

import Mathlib
import Definitions.Def_SpecActions_model

open Finset SpecActions

/-- The closed form Appendix A derives for the expected hit counter. -/
private theorem hits_eq_closed (p : ℝ) (hp : 1 + p ≠ 0) (n : ℕ) :
    hits p n = hitsClosed p n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n with
    | 0 => simp [hits, hitsClosed]
    | 1 =>
      simp only [hits, hitsClosed, Nat.cast_one, pow_one]
      field_simp
      ring
    | (k + 2) =>
      rw [hits, ih k (by omega), ih (k + 1) (by omega)]
      unfold hitsClosed
      have h1 : (-p) ^ (k + 1) = -p * (-p) ^ k := by ring
      have h2 : (-p) ^ (k + 2) = p ^ 2 * (-p) ^ k := by ring
      rw [h1, h2]
      push_cast
      field_simp
      ring

theorem solution (T : ℕ) (α β pk kt : ℝ) (hT : 1 ≤ T)
    (hα : 0 < α) (hβ : 0 < β) (hpk0 : 0 ≤ pk) (hpk1 : pk ≤ 1) :
    (specCost T α β pk kt - seqCost T β) / seqCost T β
      = kt - (1 / (T : ℝ)) * (kt + α / (α + β)) *
          (((T : ℝ) - 1) * pk / (1 + pk)
            + pk ^ 2 / (1 + pk) ^ 2
            - pk ^ 2 / (1 + pk) ^ 2 * (-pk) ^ (T - 1)) := by
  have hT0 : (0 : ℝ) < (T : ℝ) := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hT
  have hpkne : (1 : ℝ) + pk ≠ 0 := by positivity
  have hab : α + β ≠ 0 := by positivity
  have hcast : ((T - 1 : ℕ) : ℝ) = (T : ℝ) - 1 := by
    rw [Nat.cast_sub hT, Nat.cast_one]
  unfold specCost seqCost
  rw [hits_eq_closed pk hpkne]
  unfold hitsClosed
  rw [hcast]
  field_simp
  ring
