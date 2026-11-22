-- Prove2me | solution 1 for SZ.eventually_composite
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T20:55:00.864826+00:00
-- url     : https://prove2.me/submissions/28e5ed09-7ea3-41b2-81d0-55d24c9db35f

import Definitions.Def_SZ_PellDesign
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.RingTheory.Int.Basic
import Definitions.Def_SZ_QuadraticDesign
import Theorems.Thm_SZ_tendsto_design
import Theorems.Thm_SZ_dvd_floor_of_neg


set_option autoImplicit false
open SZ
open Real Filter
variable {α β : ℝ} {a b : ℤ}
namespace SZ
theorem _root_.solution {m : ℤ} (h : Pair α β a b) (hβ : β < 0) (hm : 2 ≤ m)
    (ha : m ∣ a) (hb : m ∣ (b - 1)) :
    ∀ᶠ n in atTop, ¬ Prime ⌊xiDesign α β * α ^ n⌋ ∧ 1 < ⌊xiDesign α β * α ^ n⌋ := by
  have hgt := (tendsto_design h hβ).eventually_gt_atTop ((m : ℝ) + 1)
  refine hgt.mono fun n hn => ?_
  set x : ℤ := ⌊xiDesign α β * α ^ n⌋ with hx
  have hfl : ((m : ℝ) + 1) - 1 < (x : ℝ) :=
    lt_of_lt_of_le (by linarith) (Int.sub_one_lt_floor _ |>.le)
  have hmx : m < x := by exact_mod_cast (by linarith : (m : ℝ) < (x : ℝ))
  have hdvd : m ∣ x := dvd_floor_of_neg h hβ ha hb n
  refine ⟨fun hp => ?_, by omega⟩
  have hpn : Nat.Prime x.natAbs := Int.prime_iff_natAbs_prime.mp hp
  have hmd : m.natAbs ∣ x.natAbs := Int.natAbs_dvd_natAbs.mpr hdvd
  rcases hpn.eq_one_or_self_of_dvd _ hmd with h1 | h1 <;> omega
end SZ
