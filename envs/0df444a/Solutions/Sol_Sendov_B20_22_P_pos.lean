-- Prove2me | solution 1 for Sendov.B20_22.P_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T18:26:59.190725+00:00
-- url     : https://prove2.me/submissions/bdb0ea4e-3661-4920-ad73-15a2932c1697

import Definitions.Def_Sendov_FiniteRange_Batch
import Definitions.Def_Sendov_FiniteRange_PackBridge
import Definitions.Def_Sendov_FiniteRange_Degree20_22

set_option autoImplicit false
set_option linter.style.longLine false
set_option maxRecDepth 4000000
open Sendov
open Sendov.B20_22
set_option maxHeartbeats 2000000
namespace Sendov.B20_22
theorem _root_.solution {α : ℝ} (hα : 0 ≤ α) (hα' : α ≤ 21 / 2) :
    0 < 721140310389707127738 + 2170180610909239016088 * α + 2889750967198268814324 * α ^ 2 + 2227128338977232972904 * α ^ 3 + 1085997068794302710391 * α ^ 4 + 339049376116278228288 * α ^ 5 + 60509700204282383346 * α ^ 6 - 1038039442012938636 * α ^ 7 - 14060791839010189905 * α ^ 8 + 1774506642858471852 * α ^ 9 + 45855210342618468 * α ^ 10 + 226538249017920 * α ^ 11 - 222291771124416 * α ^ 12 - 18538380993792 * α ^ 13 - 787852835840 * α ^ 14 - 20286313472 * α ^ 15 - 320448768 * α ^ 16 - 2874368 * α ^ 17 - 11264 * α ^ 18 := by
  have hu : (0 : ℝ) ≤ 21 - 2 * α := by linarith
  have h0 : (0:ℝ) ≤ 721140310389707127738 * (21 - 2 * α) ^ 18 :=
    mul_nonneg (by norm_num) (pow_nonneg hu 18)
  have h1 : (0:ℝ) ≤ 71534844003123475936416 * α ^ 1 * (21 - 2 * α) ^ 17 :=
    mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hα 1)) (pow_nonneg hu 17)
  have h2 : (0:ℝ) ≤ 3265227002682133966779372 * α ^ 2 * (21 - 2 * α) ^ 16 :=
    mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hα 2)) (pow_nonneg hu 16)
  have h3 : (0:ℝ) ≤ 90905348441621278719467208 * α ^ 3 * (21 - 2 * α) ^ 15 :=
    mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hα 3)) (pow_nonneg hu 15)
  have h4 : (0:ℝ) ≤ 1724899809677710491069520311 * α ^ 4 * (21 - 2 * α) ^ 14 :=
    mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hα 4)) (pow_nonneg hu 14)
  have h5 : (0:ℝ) ≤ 23603549699659251265167149604 * α ^ 5 * (21 - 2 * α) ^ 13 :=
    mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hα 5)) (pow_nonneg hu 13)
  have h6 : (0:ℝ) ≤ 240138761499155563910895585654 * α ^ 6 * (21 - 2 * α) ^ 12 :=
    mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hα 6)) (pow_nonneg hu 12)
  have h7 : (0:ℝ) ≤ 1837366344267267569709080196468 * α ^ 7 * (21 - 2 * α) ^ 11 :=
    mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hα 7)) (pow_nonneg hu 11)
  have h8 : (0:ℝ) ≤ 10104702475479597929008103413095 * α ^ 8 * (21 - 2 * α) ^ 10 :=
    mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hα 8)) (pow_nonneg hu 10)
  have h9 : (0:ℝ) ≤ 37641802639366180553916149163576 * α ^ 9 * (21 - 2 * α) ^ 9 :=
    mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hα 9)) (pow_nonneg hu 9)
  have h10 : (0:ℝ) ≤ 88449061215859475411346373536264 * α ^ 10 * (21 - 2 * α) ^ 8 :=
    mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hα 10)) (pow_nonneg hu 8)
  have h11 : (0:ℝ) ≤ 113640861426905556745222707601920 * α ^ 11 * (21 - 2 * α) ^ 7 :=
    mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hα 11)) (pow_nonneg hu 7)
  have h12 : (0:ℝ) ≤ 55669273871103476657042199021792 * α ^ 12 * (21 - 2 * α) ^ 6 :=
    mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hα 12)) (pow_nonneg hu 6)
  have h13 : (0:ℝ) ≤ 99281941699214882417362945572096 * α ^ 13 * (21 - 2 * α) ^ 5 :=
    mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hα 13)) (pow_nonneg hu 5)
  have h14 : (0:ℝ) ≤ 654986082897929475911576119281408 * α ^ 14 * (21 - 2 * α) ^ 4 :=
    mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hα 14)) (pow_nonneg hu 4)
  have h15 : (0:ℝ) ≤ 1538940561324052318678745687107584 * α ^ 15 * (21 - 2 * α) ^ 3 :=
    mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hα 15)) (pow_nonneg hu 3)
  have h16 : (0:ℝ) ≤ 1719020178639381082845279983473152 * α ^ 16 * (21 - 2 * α) ^ 2 :=
    mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hα 16)) (pow_nonneg hu 2)
  have h17 : (0:ℝ) ≤ 910135906460129539245476343896064 * α ^ 17 * (21 - 2 * α) ^ 1 :=
    mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hα 17)) (pow_nonneg hu 1)
  have h18 : (0:ℝ) ≤ 165769381149578270034391223083008 * α ^ 18 :=
    mul_nonneg (by norm_num) (pow_nonneg hα 18)
  have hid : (21 : ℝ) ^ 18 * (721140310389707127738 + 2170180610909239016088 * α + 2889750967198268814324 * α ^ 2 + 2227128338977232972904 * α ^ 3 + 1085997068794302710391 * α ^ 4 + 339049376116278228288 * α ^ 5 + 60509700204282383346 * α ^ 6 - 1038039442012938636 * α ^ 7 - 14060791839010189905 * α ^ 8 + 1774506642858471852 * α ^ 9 + 45855210342618468 * α ^ 10 + 226538249017920 * α ^ 11 - 222291771124416 * α ^ 12 - 18538380993792 * α ^ 13 - 787852835840 * α ^ 14 - 20286313472 * α ^ 15 - 320448768 * α ^ 16 - 2874368 * α ^ 17 - 11264 * α ^ 18) = 721140310389707127738 * (21 - 2 * α) ^ 18 + 71534844003123475936416 * α ^ 1 * (21 - 2 * α) ^ 17 + 3265227002682133966779372 * α ^ 2 * (21 - 2 * α) ^ 16 + 90905348441621278719467208 * α ^ 3 * (21 - 2 * α) ^ 15 + 1724899809677710491069520311 * α ^ 4 * (21 - 2 * α) ^ 14 + 23603549699659251265167149604 * α ^ 5 * (21 - 2 * α) ^ 13 + 240138761499155563910895585654 * α ^ 6 * (21 - 2 * α) ^ 12 + 1837366344267267569709080196468 * α ^ 7 * (21 - 2 * α) ^ 11 + 10104702475479597929008103413095 * α ^ 8 * (21 - 2 * α) ^ 10 + 37641802639366180553916149163576 * α ^ 9 * (21 - 2 * α) ^ 9 + 88449061215859475411346373536264 * α ^ 10 * (21 - 2 * α) ^ 8 + 113640861426905556745222707601920 * α ^ 11 * (21 - 2 * α) ^ 7 + 55669273871103476657042199021792 * α ^ 12 * (21 - 2 * α) ^ 6 + 99281941699214882417362945572096 * α ^ 13 * (21 - 2 * α) ^ 5 + 654986082897929475911576119281408 * α ^ 14 * (21 - 2 * α) ^ 4 + 1538940561324052318678745687107584 * α ^ 15 * (21 - 2 * α) ^ 3 + 1719020178639381082845279983473152 * α ^ 16 * (21 - 2 * α) ^ 2 + 910135906460129539245476343896064 * α ^ 17 * (21 - 2 * α) ^ 1 + 165769381149578270034391223083008 * α ^ 18 := by
    ring
  rcases le_total α (21 / (2 * 2)) with h | h
  · have hpos : (0 : ℝ) < 721140310389707127738 * (21 - 2 * α) ^ 18 :=
      mul_pos (by norm_num) (pow_pos (by linarith) 18)
    linarith
  · have hpos : (0 : ℝ) < 165769381149578270034391223083008 * α ^ 18 :=
      mul_pos (by norm_num) (pow_pos (by linarith) 18)
    linarith
end Sendov.B20_22
