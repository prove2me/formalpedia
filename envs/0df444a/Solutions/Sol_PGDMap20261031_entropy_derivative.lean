-- Prove2me | solution 1 for PGDMap20261031.entropy_derivative
-- status  : ACCEPTED   (prove)
-- author  : @Somehow
-- created : 2026-10-31T13:43:53.389402+00:00
-- url     : https://prove2.me/submissions/35b0396f-94e1-462c-ab8d-063c7ee93bed

import Mathlib.Tactic
import Definitions.Def_PGDMap20261031_Entropy

open PGDMap20261031
open scoped BigOperators

private lemma entropy_hasDerivAt (t : ℝ) (ht : t ∈ Set.Ioo (-1 : ℝ) 1) :
    HasDerivAt entropy (artanh t) t := by
  have hp : HasDerivAt (fun x : ℝ => 1 + x) 1 t := (hasDerivAt_id t).const_add 1
  have hm : HasDerivAt (fun x : ℝ => 1 - x) (-1) t := (hasDerivAt_id t).const_sub 1
  have hplus : 1 + t ≠ 0 := ne_of_gt (by linarith [ht.1])
  have hminus : 1 - t ≠ 0 := ne_of_gt (by linarith [ht.2])
  convert ((hp.mul (hp.log hplus)).add (hm.mul (hm.log hminus))).div_const 2 using 1
    <;> try rfl
  unfold artanh
  field_simp [hplus, hminus]
  <;> ring

theorem solution : EntropyDerivativeClaim := by
  intro M ell t ht
  have hmix : HasDerivAt (mixtureValue M) (mixtureSlope M t) t := by
    unfold mixtureValue mixtureSlope
    apply HasDerivAt.fun_sum
    intro j _
    have hspos : 0 < Real.sqrt (M.a j) := Real.sqrt_pos.mpr (M.a_pos j)
    have hslt : Real.sqrt (M.a j) < 1 := by
      nlinarith [Real.sq_sqrt (le_of_lt (M.a_pos j)), M.a_lt_one j]
    have hscaled : Real.sqrt (M.a j) * t ∈ Set.Ioo (-1 : ℝ) 1 := by
      constructor
      · nlinarith [mul_lt_mul_of_pos_left ht.1 hspos]
      · nlinarith [mul_lt_mul_of_pos_left ht.2 hspos]
    convert ((entropy_hasDerivAt _ hscaled).comp t
      ((hasDerivAt_id t).const_mul (Real.sqrt (M.a j)))).const_mul (M.weight j) using 1
      <;> first | rfl | ring
  have h := (hmix.add ((entropy_hasDerivAt t ht).const_mul M.lambda)).add
    ((hasDerivAt_id t).const_mul ell)
  convert h.deriv using 1 <;> first | rfl | simp
