-- Prove2me | solution 1 for SZ.fract_silver
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T20:55:18.741021+00:00
-- url     : https://prove2.me/submissions/d816c4db-cc9f-447a-b525-895a7d5f99ce

import Definitions.Def_SZ_PellDesign
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Definitions.Def_SZ_Silver
import Theorems.Thm_SZ_silver_pair
import Theorems.Thm_SZ_silver_conj_neg
import Theorems.Thm_SZ_xiDesign_silver
import Theorems.Thm_P2M_SZ_xiDesign__lt_one_4e35a34576eb
import Theorems.Thm_P2M_SZ_xiDesign__pos_7fd4c80a1ef7
import Theorems.Thm_P2M_SZ_xiDesign_seed__46b539b85d21
import Theorems.Thm_P2M_SZ_xiDesign_seed__77c5a5c95eea
import Theorems.Thm_SZ_Pair_sq_alpha
import Theorems.Thm_SZ_Pair_sq_beta
import Theorems.Thm_SZ_floorNeg
import Theorems.Thm_SZ_rec2_real


set_option autoImplicit false
open SZ
open Real
namespace SZ
theorem _root_.solution (n : ℕ) :
    |Int.fract ((2 - Real.sqrt 2) / 4 * (1 + Real.sqrt 2) ^ n)
      - (if n % 2 = 0 then 1 else 0)|
      ≤ |(1 : ℝ) - Real.sqrt 2| ^ n := by
  set α : ℝ := 1 + Real.sqrt 2
  set β : ℝ := 1 - Real.sqrt 2
  have hp := xiDesign'_pos silver_pair
  have hlt := xiDesign'_lt_one silver_pair silver_conj_neg
  have hid : xiDesign α β * α ^ n + xiDesign' α β * β ^ n = (rec2 2 1 1 0 n : ℝ) :=
    rec2_real silver_pair.sq_alpha silver_pair.sq_beta (xiDesign_seed₀ silver_pair)
      (xiDesign_seed₁ silver_pair) n
  rw [← xiDesign_silver, Int.fract, floorNeg silver_pair silver_conj_neg n]
  have hval : xiDesign α β * α ^ n
      = (rec2 2 1 1 0 n : ℝ) - xiDesign' α β * β ^ n := by linarith
  rw [hval]
  push_cast
  have hb : |xiDesign' α β * β ^ n| ≤ |β| ^ n := by
    rw [abs_mul, abs_of_pos hp, ← abs_pow]
    exact mul_le_of_le_one_left (abs_nonneg _) hlt.le
  rcases Nat.even_or_odd n with he | ho
  · rw [if_pos (Nat.even_iff.mp he)]
    calc |(rec2 2 1 1 0 n : ℝ) - xiDesign' α β * β ^ n - ((rec2 2 1 1 0 n : ℝ) - 1) - 1|
        = |xiDesign' α β * β ^ n| := by rw [show (rec2 2 1 1 0 n : ℝ)
            - xiDesign' α β * β ^ n - ((rec2 2 1 1 0 n : ℝ) - 1) - 1
            = -(xiDesign' α β * β ^ n) by ring, abs_neg]
      _ ≤ |β| ^ n := hb
  · have hn2 : n % 2 = 1 := Nat.odd_iff.mp ho
    rw [if_neg (by omega : ¬ n % 2 = 0)]
    calc |(rec2 2 1 1 0 n : ℝ) - xiDesign' α β * β ^ n - ((rec2 2 1 1 0 n : ℝ) - 0) - 0|
        = |xiDesign' α β * β ^ n| := by rw [show (rec2 2 1 1 0 n : ℝ)
            - xiDesign' α β * β ^ n - ((rec2 2 1 1 0 n : ℝ) - 0) - 0
            = -(xiDesign' α β * β ^ n) by ring, abs_neg]
      _ ≤ |β| ^ n := hb
end SZ
