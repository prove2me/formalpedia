-- Prove2me | solution 1 for TarchaBraids.thm_3_15_adjacent_raw_zero_endpoints_v1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-21T08:18:38.534817+00:00
-- url     : https://prove2.me/submissions/51563b80-15c7-403e-9c21-454a10ba11c8

import Mathlib
import Definitions.Def_TarchaBraids_adjacent_path_data_v1

namespace TarchaBraids

open BraidsLinksMCG


lemma halfTwistConfig_zero_fun (n : ℕ) (i : Fin (n - 1)) :
    (halfTwistConfig n i 0).1 = (baseOrdered n).1 :=
  congrArg Subtype.val (halfTwistConfig_zero n i)

lemma leftBraidFun_zero (n : ℕ) (i j : Fin (n - 1)) :
    leftBraidFun n i j 0 = (baseOrdered n).1 := by
  funext k
  rw [show leftBraidFun n i j 0 k = halfTwistFun n i 0 k by simp [leftBraidFun]]
  change (halfTwistConfig n i 0).1 k = (baseOrdered n).1 k
  exact congrFun (halfTwistConfig_zero_fun n i) k

lemma rightBraidFun_zero (n : ℕ) (i j : Fin (n - 1)) :
    rightBraidFun n i j 0 = (baseOrdered n).1 := by
  funext k
  rw [show rightBraidFun n i j 0 k = halfTwistFun n j 0 k by simp [rightBraidFun]]
  change (halfTwistConfig n j 0).1 k = (baseOrdered n).1 k
  exact congrFun (halfTwistConfig_zero_fun n j) k

lemma outerRotateFun_zero (n : ℕ) (i : Fin (n - 1)) :
    outerRotateFun n i 0 = (baseOrdered n).1 := by
  funext k
  simp only [outerRotateFun]
  split_ifs <;> simp_all [twistPoint, baseOrdered] <;> push_cast <;> ring


end TarchaBraids

open BraidsLinksMCG TarchaBraids
theorem solution :
    (∀ (n : ℕ) (i j : Fin (n - 1)),
      leftBraidFun n i j 0 = (baseOrdered n).1) ∧
    (∀ (n : ℕ) (i j : Fin (n - 1)),
      rightBraidFun n i j 0 = (baseOrdered n).1) ∧
    (∀ (n : ℕ) (i : Fin (n - 1)),
      outerRotateFun n i 0 = (baseOrdered n).1) := by
  exact ⟨leftBraidFun_zero, ⟨rightBraidFun_zero, outerRotateFun_zero⟩⟩

