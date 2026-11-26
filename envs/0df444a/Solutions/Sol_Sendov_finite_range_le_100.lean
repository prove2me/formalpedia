-- Prove2me | solution 1 for Sendov.finite_range_le_100
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T20:28:10.428286+00:00
-- url     : https://prove2.me/submissions/a7a9131f-1e0d-4607-b6e5-4390ff18ccf1

import Definitions.Def_Sendov_FiniteRange_Degree5
import Definitions.Def_Sendov_FiniteRange_Degree7
import Definitions.Def_Sendov_FiniteRange_Degree6_6
import Definitions.Def_Sendov_FiniteRange_Degree8_9
import Definitions.Def_Sendov_FiniteRange_Degree10_11
import Definitions.Def_Sendov_FiniteRange_Degree12_13
import Definitions.Def_Sendov_FiniteRange_Degree14_15
import Definitions.Def_Sendov_FiniteRange_Degree16_18
import Definitions.Def_Sendov_FiniteRange_Degree18_20
import Definitions.Def_Sendov_FiniteRange_Degree20_22
import Definitions.Def_Sendov_FiniteRange_Degree22_24
import Definitions.Def_Sendov_FiniteRange_Degree24_26
import Definitions.Def_Sendov_FiniteRange_Degree26_27
import Definitions.Def_Sendov_FiniteRange_Degree28_29
import Definitions.Def_Sendov_FiniteRange_Degree30_31
import Definitions.Def_Sendov_FiniteRange_Degree32_33
import Definitions.Def_Sendov_FiniteRange_Degree34_35
import Definitions.Def_Sendov_FiniteRange_Degree36_37
import Definitions.Def_Sendov_FiniteRange_Degree38_39
import Definitions.Def_Sendov_FiniteRange_Degree40_41
import Definitions.Def_Sendov_FiniteRange_Degree42_43
import Definitions.Def_Sendov_FiniteRange_Degree44_45
import Definitions.Def_Sendov_FiniteRange_Degree46_47
import Definitions.Def_Sendov_FiniteRange_Degree48_49
import Definitions.Def_Sendov_FiniteRange_Degree50_51
import Definitions.Def_Sendov_FiniteRange_Degree52_53
import Definitions.Def_Sendov_FiniteRange_Degree54_55
import Definitions.Def_Sendov_FiniteRange_Degree56_58
import Definitions.Def_Sendov_FiniteRange_Degree58_60
import Definitions.Def_Sendov_FiniteRange_Degree60_63
import Definitions.Def_Sendov_FiniteRange_Degree64_69
import Definitions.Def_Sendov_FiniteRange_Degree70_79
import Definitions.Def_Sendov_FiniteRange_Degree80_100
import Definitions.Def_Sendov_FiniteRange_Cover
import Theorems.Thm_Sendov_B10_11_finite_range
import Theorems.Thm_Sendov_B12_13_finite_range
import Theorems.Thm_Sendov_B14_15_finite_range
import Theorems.Thm_Sendov_B16_18_finite_range
import Theorems.Thm_Sendov_B18_20_finite_range
import Theorems.Thm_Sendov_B20_22_finite_range
import Theorems.Thm_Sendov_B22_24_finite_range
import Theorems.Thm_Sendov_B24_26_finite_range
import Theorems.Thm_Sendov_B26_27_finite_range
import Theorems.Thm_Sendov_B28_29_finite_range
import Theorems.Thm_Sendov_B30_31_finite_range
import Theorems.Thm_Sendov_B32_33_finite_range
import Theorems.Thm_Sendov_B34_35_finite_range
import Theorems.Thm_Sendov_B36_37_finite_range
import Theorems.Thm_Sendov_B38_39_finite_range
import Theorems.Thm_Sendov_B40_41_finite_range
import Theorems.Thm_Sendov_B42_43_finite_range
import Theorems.Thm_Sendov_B44_45_finite_range
import Theorems.Thm_Sendov_B46_47_finite_range
import Theorems.Thm_Sendov_B48_49_finite_range
import Theorems.Thm_Sendov_B50_51_finite_range
import Theorems.Thm_Sendov_B52_53_finite_range
import Theorems.Thm_Sendov_B54_55_finite_range
import Theorems.Thm_Sendov_B56_58_finite_range
import Theorems.Thm_Sendov_B58_60_finite_range
import Theorems.Thm_Sendov_B60_63_finite_range
import Theorems.Thm_Sendov_B64_69_finite_range
import Theorems.Thm_Sendov_B6_6_finite_range
import Theorems.Thm_Sendov_B70_79_finite_range
import Theorems.Thm_Sendov_B80_100_finite_range
import Theorems.Thm_Sendov_B8_9_finite_range
import Theorems.Thm_Sendov_finite_range_five
import Theorems.Thm_Sendov_finite_range_seven


set_option autoImplicit false
open Sendov
variable {α : ℝ}
namespace Sendov
theorem _root_.solution {n : ℕ} (h0 : 5 ≤ n) (h1 : n ≤ 100)
    (hα : 0 ≤ α) (hα' : α ≤ 17) (hfeas : c n α ^ 2 ≤ A n α) : R n α < 1 := by
  -- degrees 5..5
  rcases Nat.lt_or_ge n 6 with h | h
  · obtain rfl : n = 5 := by omega
    exact finite_range_five hα hfeas
  -- degrees 6..6
  rcases Nat.lt_or_ge n 7 with h | h
  · exact B6_6.finite_range (by omega) (by omega) hα hα' hfeas
  -- degrees 7..7
  rcases Nat.lt_or_ge n 8 with h | h
  · obtain rfl : n = 7 := by omega
    exact finite_range_seven hα hfeas
  -- degrees 8..9
  rcases Nat.lt_or_ge n 10 with h | h
  · exact B8_9.finite_range (by omega) (by omega) hα hα' hfeas
  -- degrees 10..11
  rcases Nat.lt_or_ge n 12 with h | h
  · exact B10_11.finite_range (by omega) (by omega) hα hα' hfeas
  -- degrees 12..13
  rcases Nat.lt_or_ge n 14 with h | h
  · exact B12_13.finite_range (by omega) (by omega) hα hα' hfeas
  -- degrees 14..15
  rcases Nat.lt_or_ge n 16 with h | h
  · exact B14_15.finite_range (by omega) (by omega) hα hα' hfeas
  -- degrees 16..18
  rcases Nat.lt_or_ge n 19 with h | h
  · exact B16_18.finite_range (by omega) (by omega) hα hα' hfeas
  -- degrees 19..20
  rcases Nat.lt_or_ge n 21 with h | h
  · exact B18_20.finite_range (by omega) (by omega) hα hα' hfeas
  -- degrees 21..22
  rcases Nat.lt_or_ge n 23 with h | h
  · exact B20_22.finite_range (by omega) (by omega) hα hα' hfeas
  -- degrees 23..24
  rcases Nat.lt_or_ge n 25 with h | h
  · exact B22_24.finite_range (by omega) (by omega) hα hα' hfeas
  -- degrees 25..26
  rcases Nat.lt_or_ge n 27 with h | h
  · exact B24_26.finite_range (by omega) (by omega) hα hα' hfeas
  -- degrees 27..27
  rcases Nat.lt_or_ge n 28 with h | h
  · exact B26_27.finite_range (by omega) (by omega) hα hα' hfeas
  -- degrees 28..29
  rcases Nat.lt_or_ge n 30 with h | h
  · exact B28_29.finite_range (by omega) (by omega) hα hα' hfeas
  -- degrees 30..31
  rcases Nat.lt_or_ge n 32 with h | h
  · exact B30_31.finite_range (by omega) (by omega) hα hα' hfeas
  -- degrees 32..33
  rcases Nat.lt_or_ge n 34 with h | h
  · exact B32_33.finite_range (by omega) (by omega) hα hα' hfeas
  -- degrees 34..35
  rcases Nat.lt_or_ge n 36 with h | h
  · exact B34_35.finite_range (by omega) (by omega) hα hα' hfeas
  -- degrees 36..37
  rcases Nat.lt_or_ge n 38 with h | h
  · exact B36_37.finite_range (by omega) (by omega) hα hα' hfeas
  -- degrees 38..39
  rcases Nat.lt_or_ge n 40 with h | h
  · exact B38_39.finite_range (by omega) (by omega) hα hα' hfeas
  -- degrees 40..41
  rcases Nat.lt_or_ge n 42 with h | h
  · exact B40_41.finite_range (by omega) (by omega) hα hα' hfeas
  -- degrees 42..43
  rcases Nat.lt_or_ge n 44 with h | h
  · exact B42_43.finite_range (by omega) (by omega) hα hα' hfeas
  -- degrees 44..45
  rcases Nat.lt_or_ge n 46 with h | h
  · exact B44_45.finite_range (by omega) (by omega) hα hα' hfeas
  -- degrees 46..47
  rcases Nat.lt_or_ge n 48 with h | h
  · exact B46_47.finite_range (by omega) (by omega) hα hα' hfeas
  -- degrees 48..49
  rcases Nat.lt_or_ge n 50 with h | h
  · exact B48_49.finite_range (by omega) (by omega) hα hα' hfeas
  -- degrees 50..51
  rcases Nat.lt_or_ge n 52 with h | h
  · exact B50_51.finite_range (by omega) (by omega) hα hα' hfeas
  -- degrees 52..53
  rcases Nat.lt_or_ge n 54 with h | h
  · exact B52_53.finite_range (by omega) (by omega) hα hα' hfeas
  -- degrees 54..55
  rcases Nat.lt_or_ge n 56 with h | h
  · exact B54_55.finite_range (by omega) (by omega) hα hα' hfeas
  -- degrees 56..58
  rcases Nat.lt_or_ge n 59 with h | h
  · exact B56_58.finite_range (by omega) (by omega) hα hα' hfeas
  -- degrees 59..60
  rcases Nat.lt_or_ge n 61 with h | h
  · exact B58_60.finite_range (by omega) (by omega) hα hα' hfeas
  -- degrees 61..63
  rcases Nat.lt_or_ge n 64 with h | h
  · exact B60_63.finite_range (by omega) (by omega) hα hα' hfeas
  -- degrees 64..69
  rcases Nat.lt_or_ge n 70 with h | h
  · exact B64_69.finite_range (by omega) (by omega) hα hα' hfeas
  -- degrees 70..79
  rcases Nat.lt_or_ge n 80 with h | h
  · exact B70_79.finite_range (by omega) (by omega) hα hα' hfeas
  -- degrees 80..100
  exact B80_100.finite_range (by omega) (by omega) hα hα' hfeas
end Sendov
