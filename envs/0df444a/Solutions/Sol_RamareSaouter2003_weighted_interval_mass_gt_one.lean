-- Prove2me | solution 1 for RamareSaouter2003.weighted_interval_mass_gt_one
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-09-25T12:57:01.127092+00:00
-- url     : https://prove2.me/submissions/7326d13d-3319-492d-81dc-3450170bb1a7
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_RamareSaouter2003_prime_interval_large_range
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Lemmas
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Complex.ExponentialBounds

theorem solution (x : Real)
    (hx : (10 : Real) ^ (20 : Nat) <= x) :
    1 < Finset.sum (Finset.range (Nat.floor x + 1))
      (fun p => if p.Prime /\ x * (1 - 1 / 81353847) < (p : Real) /\ (p : Real) <= x
        then Real.log (p : Real) else 0) := by
  classical
  obtain ⟨p, hp, hlow, hhigh⟩ :=
    RamareSaouter2003.prime_interval_large_range x hx
  have hxpos : 0 < x := by
    have : (0 : Real) < (10 : Real) ^ (20 : Nat) := by positivity
    exact lt_of_lt_of_le this hx
  have hfactor : (1 : Real) / 2 < 1 - 1 / 81353847 := by norm_num
  have hp_large : (4 : Real) < (p : Real) := by
    have hmul := mul_lt_mul_of_pos_left hfactor hxpos
    nlinarith [hlow, hx]
  have hp4 : 4 < p := by exact_mod_cast hp_large
  have hp3 : 3 < p := by omega
  have hexp : Real.exp 1 < (p : Real) := by
    exact lt_trans Real.exp_one_lt_three (by exact_mod_cast hp3)
  have hlog : 1 < Real.log (p : Real) := by
    apply (Real.lt_log_iff_exp_lt (by positivity)).2
    exact hexp
  have hp_mem : p ∈ Finset.range (Nat.floor x + 1) := by
    apply Finset.mem_range.mpr
    have hfloor : p ≤ Nat.floor x := Nat.le_floor hhigh
    omega
  let f : Nat → Real := fun q =>
    if q.Prime /\ x * (1 - 1 / 81353847) < (q : Real) /\ (q : Real) <= x
    then Real.log (q : Real) else 0
  have hsum_lower : f p ≤ Finset.sum (Finset.range (Nat.floor x + 1)) f := by
    exact Finset.single_le_sum (s := Finset.range (Nat.floor x + 1)) (f := f)
      (by
        intro q hq
        change 0 ≤ (if q.Prime /\ x * (1 - 1 / 81353847) < (q : Real) /\ (q : Real) <= x
          then Real.log (q : Real) else 0)
        by_cases hcond : q.Prime /\ x * (1 - 1 / 81353847) < (q : Real) /\ (q : Real) <= x
        · rw [if_pos hcond]
          exact Real.log_natCast_nonneg q
        · rw [if_neg hcond]) hp_mem
  have hfp : f p = Real.log (p : Real) := by
    change (if p.Prime /\ x * (1 - 1 / 81353847) < (p : Real) /\ (p : Real) <= x
      then Real.log (p : Real) else 0) = _
    rw [if_pos ⟨hp, hlow, hhigh⟩]
  rw [hfp] at hsum_lower
  simpa only [f] using (lt_of_lt_of_le hlog hsum_lower)
