-- Prove2me | solution 1 for TaoFivePrimes.ramare_squarefree_totient_sum_le_small
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-19T19:22:48.747303+00:00
-- url     : https://prove2.me/submissions/9bd20064-deb0-4e31-88d4-000f2a22b4e0

import Theorems.Thm_RamareFiniteBounds_endpoint_prefixes
import Definitions.Def_RamareFiniteBounds
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Lean.Elab.Tactic.Omega
import Mathlib.Data.Nat.Totient
import Mathlib.Data.Nat.Squarefree
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Order.Interval.Finset.Nat


open RamareFiniteBounds
open scoped BigOperators

namespace RamareFiniteBoundsAnalytic

/-- A rational lower bound from the nonnegative odd-power logarithm series. -/
private def logLower (x : ℚ) (terms : ℕ) : ℚ :=
  2 * ∑ i ∈ Finset.range terms,
    ((x - 1) / (x + 1)) ^ (2 * i + 1) / (2 * i + 1 : ℕ)

private theorem logLower_le (x : ℚ) (hx : 1 ≤ x) (terms : ℕ) :
    (logLower x terms : ℝ) ≤ Real.log (x : ℝ) := by
  have hxR : (1 : ℝ) ≤ x := by exact_mod_cast hx
  have hden : (0 : ℝ) < (x : ℝ) + 1 := by linarith
  have hnonneg : (0 : ℝ) ≤ ((x : ℝ) - 1) / ((x : ℝ) + 1) :=
    div_nonneg (by linarith) hden.le
  have hlt : ((x : ℝ) - 1) / ((x : ℝ) + 1) < 1 := by
    apply (div_lt_one hden).2
    linarith
  have hratio :
      (1 + ((x : ℝ) - 1) / ((x : ℝ) + 1)) /
        (1 - ((x : ℝ) - 1) / ((x : ℝ) + 1)) = (x : ℝ) := by
    field_simp
    ring
  have h := Real.sum_range_le_log_div hnonneg hlt terms
  rw [hratio] at h
  unfold logLower
  push_cast
  linarith

/-- Range reduction keeps the logarithm-series argument at most one third
when `2^k ≤ N ≤ 2^(k+1)`. Only the lower inequality is needed for soundness. -/
private def logLowerNat (N k terms : ℕ) : ℚ :=
  (k : ℚ) * logLower 2 terms + logLower ((N : ℚ) / 2 ^ k) terms

private theorem logLowerNat_le (N k terms : ℕ) (hN : 2 ^ k ≤ N) :
    (logLowerNat N k terms : ℝ) ≤ Real.log (N : ℝ) := by
  have hpow : (0 : ℚ) < 2 ^ k := by positivity
  have hpowR : (0 : ℝ) < 2 ^ k := by positivity
  have hNpos : 0 < N := lt_of_lt_of_le (by positivity) hN
  have hNposR : (0 : ℝ) < N := by exact_mod_cast hNpos
  have hratio : (1 : ℚ) ≤ (N : ℚ) / 2 ^ k := by
    apply (le_div_iff₀ hpow).2
    simpa using (show (2 : ℚ) ^ k ≤ N by exact_mod_cast hN)
  have htwo := logLower_le 2 (by norm_num) terms
  norm_num at htwo
  have hrest := logLower_le ((N : ℚ) / 2 ^ k) hratio terms
  have hmult := mul_le_mul_of_nonneg_left htwo (show (0 : ℝ) ≤ k by positivity)
  have hid : (2 : ℝ) ^ k * ((N : ℝ) / 2 ^ k) = N := by
    field_simp
  have hlog := Real.log_mul hpowR.ne' (div_pos hNposR hpowR).ne'
  rw [hid, Real.log_pow] at hlog
  unfold logLowerNat
  push_cast at hrest ⊢
  linarith

end RamareFiniteBoundsAnalytic


/-!
Generated from the frozen floor-plus-one interval table. The numbers named
`upper` are certificate inputs here: this file proves their logarithm endpoint
inequalities, not that they bound any arithmetic prefix sum.
-/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace RamareFiniteBoundsAnalytic

private theorem endpoint_log_sound (a k U : ℕ) (hpow : 2 ^ k ≤ a)
    (hcert : (U : ℚ) / 10000000000 ≤ logLowerNat a k 9 + (14709 : ℚ) / 10000) :
    (U : ℝ) / 10000000000 ≤ Real.log (a : ℝ) + (14709 : ℝ) / 10000 := by
  have hreal : (U : ℝ) / 10000000000 ≤
      (logLowerNat a k 9 : ℝ) + (14709 : ℝ) / 10000 := by
    have hcast := (Rat.cast_le (K := ℝ)).2 hcert
    simpa only [Rat.cast_div, Rat.cast_add, Rat.cast_natCast, Rat.cast_ofNat] using hcast
  exact hreal.trans (add_le_add (logLowerNat_le a k 9 hpow) le_rfl)

private theorem logEndpoints_ranges : ∀ e ∈ logEndpoints,
    1 ≤ e.lo ∧ e.lo ≤ e.hi ∧ e.hi ≤ 142300 ∧ 2 ^ e.exponent ≤ e.lo := by
  decide +kernel

private theorem endpoint_000 :
    ((10000000001 : ℕ) : ℝ) / 10000000000 ≤ Real.log ((1 : ℕ) : ℝ) + (14709 : ℝ) / 10000 := by
  exact endpoint_log_sound 1 0 10000000001 (by decide +kernel) (by decide +kernel)

private theorem endpoint_001 :
    ((20000000002 : ℕ) : ℝ) / 10000000000 ≤ Real.log ((2 : ℕ) : ℝ) + (14709 : ℝ) / 10000 := by
  exact endpoint_log_sound 2 1 20000000002 (by decide +kernel) (by decide +kernel)

private theorem endpoint_002 :
    ((25000000003 : ℕ) : ℝ) / 10000000000 ≤ Real.log ((3 : ℕ) : ℝ) + (14709 : ℝ) / 10000 := by
  exact endpoint_log_sound 3 1 25000000003 (by decide +kernel) (by decide +kernel)

private theorem endpoint_003 :
    ((27500000004 : ℕ) : ℝ) / 10000000000 ≤ Real.log ((5 : ℕ) : ℝ) + (14709 : ℝ) / 10000 := by
  exact endpoint_log_sound 5 2 27500000004 (by decide +kernel) (by decide +kernel)

private theorem endpoint_004 :
    ((32500000005 : ℕ) : ℝ) / 10000000000 ≤ Real.log ((6 : ℕ) : ℝ) + (14709 : ℝ) / 10000 := by
  exact endpoint_log_sound 6 2 32500000005 (by decide +kernel) (by decide +kernel)

private theorem endpoint_005 :
    ((34166666672 : ℕ) : ℝ) / 10000000000 ≤ Real.log ((7 : ℕ) : ℝ) + (14709 : ℝ) / 10000 := by
  exact endpoint_log_sound 7 2 34166666672 (by decide +kernel) (by decide +kernel)

private theorem endpoint_006 :
    ((37666666674 : ℕ) : ℝ) / 10000000000 ≤ Real.log ((10 : ℕ) : ℝ) + (14709 : ℝ) / 10000 := by
  exact endpoint_log_sound 10 3 37666666674 (by decide +kernel) (by decide +kernel)

private theorem endpoint_007 :
    ((40166666675 : ℕ) : ℝ) / 10000000000 ≤ Real.log ((13 : ℕ) : ℝ) + (14709 : ℝ) / 10000 := by
  exact endpoint_log_sound 13 3 40166666675 (by decide +kernel) (by decide +kernel)

private theorem endpoint_008 :
    ((41416666676 : ℕ) : ℝ) / 10000000000 ≤ Real.log ((15 : ℕ) : ℝ) + (14709 : ℝ) / 10000 := by
  exact endpoint_log_sound 15 3 41416666676 (by decide +kernel) (by decide +kernel)

private theorem endpoint_009 :
    ((42597222233 : ℕ) : ℝ) / 10000000000 ≤ Real.log ((17 : ℕ) : ℝ) + (14709 : ℝ) / 10000 := by
  exact endpoint_log_sound 17 4 42597222233 (by decide +kernel) (by decide +kernel)

private theorem endpoint_010 :
    ((44885101023 : ℕ) : ℝ) / 10000000000 ≤ Real.log ((21 : ℕ) : ℝ) + (14709 : ℝ) / 10000 := by
  exact endpoint_log_sound 21 4 44885101023 (by decide +kernel) (by decide +kernel)

private theorem endpoint_011 :
    ((46075577215 : ℕ) : ℝ) / 10000000000 ≤ Real.log ((26 : ℕ) : ℝ) + (14709 : ℝ) / 10000 := by
  exact endpoint_log_sound 26 4 46075577215 (by decide +kernel) (by decide +kernel)

private theorem endpoint_012 :
    ((48158910551 : ℕ) : ℝ) / 10000000000 ≤ Real.log ((30 : ℕ) : ℝ) + (14709 : ℝ) / 10000 := by
  exact endpoint_log_sound 30 4 48158910551 (by decide +kernel) (by decide +kernel)

private theorem endpoint_013 :
    ((49478354997 : ℕ) : ℝ) / 10000000000 ≤ Real.log ((34 : ℕ) : ℝ) + (14709 : ℝ) / 10000 := by
  exact endpoint_log_sound 34 5 49478354997 (by decide +kernel) (by decide +kernel)

private theorem endpoint_014 :
    ((50700577221 : ℕ) : ℝ) / 10000000000 ≤ Real.log ((38 : ℕ) : ℝ) + (14709 : ℝ) / 10000 := by
  exact endpoint_log_sound 38 5 50700577221 (by decide +kernel) (by decide +kernel)

private theorem endpoint_015 :
    ((51772005794 : ℕ) : ℝ) / 10000000000 ≤ Real.log ((42 : ℕ) : ℝ) + (14709 : ℝ) / 10000 := by
  exact endpoint_log_sound 42 5 51772005794 (by decide +kernel) (by decide +kernel)

private theorem endpoint_016 :
    ((52948750248 : ℕ) : ℝ) / 10000000000 ≤ Real.log ((46 : ℕ) : ℝ) + (14709 : ℝ) / 10000 := by
  exact endpoint_log_sound 46 5 52948750248 (by decide +kernel) (by decide +kernel)

private theorem endpoint_017 :
    ((54714418014 : ℕ) : ℝ) / 10000000000 ≤ Real.log ((55 : ℕ) : ℝ) + (14709 : ℝ) / 10000 := by
  exact endpoint_log_sound 55 5 54714418014 (by decide +kernel) (by decide +kernel)

private theorem endpoint_018 :
    ((56569396372 : ℕ) : ℝ) / 10000000000 ≤ Real.log ((66 : ℕ) : ℝ) + (14709 : ℝ) / 10000 := by
  exact endpoint_log_sound 66 6 56569396372 (by decide +kernel) (by decide +kernel)

private theorem endpoint_019 :
    ((58047231296 : ℕ) : ℝ) / 10000000000 ≤ Real.log ((77 : ℕ) : ℝ) + (14709 : ℝ) / 10000 := by
  exact endpoint_log_sound 77 6 58047231296 (by decide +kernel) (by decide +kernel)

private theorem endpoint_020 :
    ((59205441507 : ℕ) : ℝ) / 10000000000 ≤ Real.log ((87 : ℕ) : ℝ) + (14709 : ℝ) / 10000 := by
  exact endpoint_log_sound 87 6 59205441507 (by decide +kernel) (by decide +kernel)

private theorem endpoint_021 :
    ((60681728572 : ℕ) : ℝ) / 10000000000 ≤ Real.log ((102 : ℕ) : ℝ) + (14709 : ℝ) / 10000 := by
  exact endpoint_log_sound 102 6 60681728572 (by decide +kernel) (by decide +kernel)

private theorem endpoint_022 :
    ((62048135877 : ℕ) : ℝ) / 10000000000 ≤ Real.log ((114 : ℕ) : ℝ) + (14709 : ℝ) / 10000 := by
  exact endpoint_log_sound 114 6 62048135877 (by decide +kernel) (by decide +kernel)

private theorem endpoint_023 :
    ((63439727577 : ℕ) : ℝ) / 10000000000 ≤ Real.log ((131 : ℕ) : ℝ) + (14709 : ℝ) / 10000 := by
  exact endpoint_log_sound 131 7 63439727577 (by decide +kernel) (by decide +kernel)

private theorem endpoint_024 :
    ((65071851278 : ℕ) : ℝ) / 10000000000 ≤ Real.log ((154 : ℕ) : ℝ) + (14709 : ℝ) / 10000 := by
  exact endpoint_log_sound 154 7 65071851278 (by decide +kernel) (by decide +kernel)

private theorem endpoint_025 :
    ((66653078926 : ℕ) : ℝ) / 10000000000 ≤ Real.log ((181 : ℕ) : ℝ) + (14709 : ℝ) / 10000 := by
  exact endpoint_log_sound 181 7 66653078926 (by decide +kernel) (by decide +kernel)

private theorem endpoint_026 :
    ((68123849868 : ℕ) : ℝ) / 10000000000 ≤ Real.log ((210 : ℕ) : ℝ) + (14709 : ℝ) / 10000 := by
  exact endpoint_log_sound 210 7 68123849868 (by decide +kernel) (by decide +kernel)

private theorem endpoint_027 :
    ((69378252149 : ℕ) : ℝ) / 10000000000 ≤ Real.log ((238 : ℕ) : ℝ) + (14709 : ℝ) / 10000 := by
  exact endpoint_log_sound 238 7 69378252149 (by decide +kernel) (by decide +kernel)

private theorem endpoint_028 :
    ((70755760372 : ℕ) : ℝ) / 10000000000 ≤ Real.log ((273 : ℕ) : ℝ) + (14709 : ℝ) / 10000 := by
  exact endpoint_log_sound 273 8 70755760372 (by decide +kernel) (by decide +kernel)

private theorem endpoint_029 :
    ((72195842919 : ℕ) : ℝ) / 10000000000 ≤ Real.log ((314 : ℕ) : ℝ) + (14709 : ℝ) / 10000 := by
  exact endpoint_log_sound 314 8 72195842919 (by decide +kernel) (by decide +kernel)

private theorem endpoint_030 :
    ((73706126532 : ℕ) : ℝ) / 10000000000 ≤ Real.log ((366 : ℕ) : ℝ) + (14709 : ℝ) / 10000 := by
  exact endpoint_log_sound 366 8 73706126532 (by decide +kernel) (by decide +kernel)

private theorem endpoint_031 :
    ((75144228761 : ℕ) : ℝ) / 10000000000 ≤ Real.log ((422 : ℕ) : ℝ) + (14709 : ℝ) / 10000 := by
  exact endpoint_log_sound 422 8 75144228761 (by decide +kernel) (by decide +kernel)

private theorem endpoint_032 :
    ((76484834138 : ℕ) : ℝ) / 10000000000 ≤ Real.log ((482 : ℕ) : ℝ) + (14709 : ℝ) / 10000 := by
  exact endpoint_log_sound 482 8 76484834138 (by decide +kernel) (by decide +kernel)

private theorem endpoint_033 :
    ((77878820124 : ℕ) : ℝ) / 10000000000 ≤ Real.log ((554 : ℕ) : ℝ) + (14709 : ℝ) / 10000 := by
  exact endpoint_log_sound 554 9 77878820124 (by decide +kernel) (by decide +kernel)

private theorem endpoint_034 :
    ((79243799040 : ℕ) : ℝ) / 10000000000 ≤ Real.log ((635 : ℕ) : ℝ) + (14709 : ℝ) / 10000 := by
  exact endpoint_log_sound 635 9 79243799040 (by decide +kernel) (by decide +kernel)

private theorem endpoint_035 :
    ((80631110893 : ℕ) : ℝ) / 10000000000 ≤ Real.log ((730 : ℕ) : ℝ) + (14709 : ℝ) / 10000 := by
  exact endpoint_log_sound 730 9 80631110893 (by decide +kernel) (by decide +kernel)

private theorem endpoint_036 :
    ((81978547871 : ℕ) : ℝ) / 10000000000 ≤ Real.log ((835 : ℕ) : ℝ) + (14709 : ℝ) / 10000 := by
  exact endpoint_log_sound 835 9 81978547871 (by decide +kernel) (by decide +kernel)

private theorem endpoint_037 :
    ((83348286055 : ℕ) : ℝ) / 10000000000 ≤ Real.log ((959 : ℕ) : ℝ) + (14709 : ℝ) / 10000 := by
  exact endpoint_log_sound 959 9 83348286055 (by decide +kernel) (by decide +kernel)

private theorem endpoint_038 :
    ((84784450761 : ℕ) : ℝ) / 10000000000 ≤ Real.log ((1106 : ℕ) : ℝ) + (14709 : ℝ) / 10000 := by
  exact endpoint_log_sound 1106 10 84784450761 (by decide +kernel) (by decide +kernel)

private theorem endpoint_039 :
    ((86168594696 : ℕ) : ℝ) / 10000000000 ≤ Real.log ((1270 : ℕ) : ℝ) + (14709 : ℝ) / 10000 := by
  exact endpoint_log_sound 1270 10 86168594696 (by decide +kernel) (by decide +kernel)

private theorem endpoint_040 :
    ((87522766859 : ℕ) : ℝ) / 10000000000 ≤ Real.log ((1454 : ℕ) : ℝ) + (14709 : ℝ) / 10000 := by
  exact endpoint_log_sound 1454 10 87522766859 (by decide +kernel) (by decide +kernel)

private theorem endpoint_041 :
    ((88860271373 : ℕ) : ℝ) / 10000000000 ≤ Real.log ((1662 : ℕ) : ℝ) + (14709 : ℝ) / 10000 := by
  exact endpoint_log_sound 1662 10 88860271373 (by decide +kernel) (by decide +kernel)

private theorem endpoint_042 :
    ((90269228769 : ℕ) : ℝ) / 10000000000 ≤ Real.log ((1914 : ℕ) : ℝ) + (14709 : ℝ) / 10000 := by
  exact endpoint_log_sound 1914 10 90269228769 (by decide +kernel) (by decide +kernel)

private theorem endpoint_043 :
    ((91678279488 : ℕ) : ℝ) / 10000000000 ≤ Real.log ((2202 : ℕ) : ℝ) + (14709 : ℝ) / 10000 := by
  exact endpoint_log_sound 2202 11 91678279488 (by decide +kernel) (by decide +kernel)

private theorem endpoint_044 :
    ((93048242808 : ℕ) : ℝ) / 10000000000 ≤ Real.log ((2526 : ℕ) : ℝ) + (14709 : ℝ) / 10000 := by
  exact endpoint_log_sound 2526 11 93048242808 (by decide +kernel) (by decide +kernel)

private theorem endpoint_045 :
    ((94449403959 : ℕ) : ℝ) / 10000000000 ≤ Real.log ((2906 : ℕ) : ℝ) + (14709 : ℝ) / 10000 := by
  exact endpoint_log_sound 2906 11 94449403959 (by decide +kernel) (by decide +kernel)

private theorem endpoint_046 :
    ((95820608345 : ℕ) : ℝ) / 10000000000 ≤ Real.log ((3333 : ℕ) : ℝ) + (14709 : ℝ) / 10000 := by
  exact endpoint_log_sound 3333 11 95820608345 (by decide +kernel) (by decide +kernel)

private theorem endpoint_047 :
    ((97213969920 : ℕ) : ℝ) / 10000000000 ≤ Real.log ((3830 : ℕ) : ℝ) + (14709 : ℝ) / 10000 := by
  exact endpoint_log_sound 3830 11 97213969920 (by decide +kernel) (by decide +kernel)

private theorem endpoint_048 :
    ((98593944130 : ℕ) : ℝ) / 10000000000 ≤ Real.log ((4397 : ℕ) : ℝ) + (14709 : ℝ) / 10000 := by
  exact endpoint_log_sound 4397 12 98593944130 (by decide +kernel) (by decide +kernel)

private theorem endpoint_049 :
    ((99957414198 : ℕ) : ℝ) / 10000000000 ≤ Real.log ((5039 : ℕ) : ℝ) + (14709 : ℝ) / 10000 := by
  exact endpoint_log_sound 5039 12 99957414198 (by decide +kernel) (by decide +kernel)

private theorem endpoint_050 :
    ((101360837942 : ℕ) : ℝ) / 10000000000 ≤ Real.log ((5798 : ℕ) : ℝ) + (14709 : ℝ) / 10000 := by
  exact endpoint_log_sound 5798 12 101360837942 (by decide +kernel) (by decide +kernel)

private theorem endpoint_051 :
    ((102749074130 : ℕ) : ℝ) / 10000000000 ≤ Real.log ((6661 : ℕ) : ℝ) + (14709 : ℝ) / 10000 := by
  exact endpoint_log_sound 6661 12 102749074130 (by decide +kernel) (by decide +kernel)

private theorem endpoint_052 :
    ((104125057472 : ℕ) : ℝ) / 10000000000 ≤ Real.log ((7647 : ℕ) : ℝ) + (14709 : ℝ) / 10000 := by
  exact endpoint_log_sound 7647 12 104125057472 (by decide +kernel) (by decide +kernel)

private theorem endpoint_053 :
    ((105506430410 : ℕ) : ℝ) / 10000000000 ≤ Real.log ((8778 : ℕ) : ℝ) + (14709 : ℝ) / 10000 := by
  exact endpoint_log_sound 8778 13 105506430410 (by decide +kernel) (by decide +kernel)

private theorem endpoint_054 :
    ((106885038573 : ℕ) : ℝ) / 10000000000 ≤ Real.log ((10074 : ℕ) : ℝ) + (14709 : ℝ) / 10000 := by
  exact endpoint_log_sound 10074 13 106885038573 (by decide +kernel) (by decide +kernel)

private theorem endpoint_055 :
    ((108270576051 : ℕ) : ℝ) / 10000000000 ≤ Real.log ((11570 : ℕ) : ℝ) + (14709 : ℝ) / 10000 := by
  exact endpoint_log_sound 11570 13 108270576051 (by decide +kernel) (by decide +kernel)

private theorem endpoint_056 :
    ((109655338876 : ℕ) : ℝ) / 10000000000 ≤ Real.log ((13289 : ℕ) : ℝ) + (14709 : ℝ) / 10000 := by
  exact endpoint_log_sound 13289 13 109655338876 (by decide +kernel) (by decide +kernel)

private theorem endpoint_057 :
    ((111040440149 : ℕ) : ℝ) / 10000000000 ≤ Real.log ((15263 : ℕ) : ℝ) + (14709 : ℝ) / 10000 := by
  exact endpoint_log_sound 15263 13 111040440149 (by decide +kernel) (by decide +kernel)

private theorem endpoint_058 :
    ((112420936661 : ℕ) : ℝ) / 10000000000 ≤ Real.log ((17522 : ℕ) : ℝ) + (14709 : ℝ) / 10000 := by
  exact endpoint_log_sound 17522 14 112420936661 (by decide +kernel) (by decide +kernel)

private theorem endpoint_059 :
    ((113802112086 : ℕ) : ℝ) / 10000000000 ≤ Real.log ((20119 : ℕ) : ℝ) + (14709 : ℝ) / 10000 := by
  exact endpoint_log_sound 20119 14 113802112086 (by decide +kernel) (by decide +kernel)

private theorem endpoint_060 :
    ((115187036893 : ℕ) : ℝ) / 10000000000 ≤ Real.log ((23106 : ℕ) : ℝ) + (14709 : ℝ) / 10000 := by
  exact endpoint_log_sound 23106 14 115187036893 (by decide +kernel) (by decide +kernel)

private theorem endpoint_061 :
    ((116570808110 : ℕ) : ℝ) / 10000000000 ≤ Real.log ((26535 : ℕ) : ℝ) + (14709 : ℝ) / 10000 := by
  exact endpoint_log_sound 26535 14 116570808110 (by decide +kernel) (by decide +kernel)

private theorem endpoint_062 :
    ((117952577160 : ℕ) : ℝ) / 10000000000 ≤ Real.log ((30466 : ℕ) : ℝ) + (14709 : ℝ) / 10000 := by
  exact endpoint_log_sound 30466 14 117952577160 (by decide +kernel) (by decide +kernel)

private theorem endpoint_063 :
    ((119336869463 : ℕ) : ℝ) / 10000000000 ≤ Real.log ((34990 : ℕ) : ℝ) + (14709 : ℝ) / 10000 := by
  exact endpoint_log_sound 34990 15 119336869463 (by decide +kernel) (by decide +kernel)

private theorem endpoint_064 :
    ((120722814528 : ℕ) : ℝ) / 10000000000 ≤ Real.log ((40191 : ℕ) : ℝ) + (14709 : ℝ) / 10000 := by
  exact endpoint_log_sound 40191 15 120722814528 (by decide +kernel) (by decide +kernel)

private theorem endpoint_065 :
    ((122104241703 : ℕ) : ℝ) / 10000000000 ≤ Real.log ((46145 : ℕ) : ℝ) + (14709 : ℝ) / 10000 := by
  exact endpoint_log_sound 46145 15 122104241703 (by decide +kernel) (by decide +kernel)

private theorem endpoint_066 :
    ((123485008269 : ℕ) : ℝ) / 10000000000 ≤ Real.log ((52977 : ℕ) : ℝ) + (14709 : ℝ) / 10000 := by
  exact endpoint_log_sound 52977 15 123485008269 (by decide +kernel) (by decide +kernel)

private theorem endpoint_067 :
    ((124867807525 : ℕ) : ℝ) / 10000000000 ≤ Real.log ((60833 : ℕ) : ℝ) + (14709 : ℝ) / 10000 := by
  exact endpoint_log_sound 60833 15 124867807525 (by decide +kernel) (by decide +kernel)

private theorem endpoint_068 :
    ((126251687858 : ℕ) : ℝ) / 10000000000 ≤ Real.log ((69862 : ℕ) : ℝ) + (14709 : ℝ) / 10000 := by
  exact endpoint_log_sound 69862 16 126251687858 (by decide +kernel) (by decide +kernel)

private theorem endpoint_069 :
    ((127638869874 : ℕ) : ℝ) / 10000000000 ≤ Real.log ((80258 : ℕ) : ℝ) + (14709 : ℝ) / 10000 := by
  exact endpoint_log_sound 80258 16 127638869874 (by decide +kernel) (by decide +kernel)

private theorem endpoint_070 :
    ((129021341399 : ℕ) : ℝ) / 10000000000 ≤ Real.log ((92157 : ℕ) : ℝ) + (14709 : ℝ) / 10000 := by
  exact endpoint_log_sound 92157 16 129021341399 (by decide +kernel) (by decide +kernel)

private theorem endpoint_071 :
    ((130403721186 : ℕ) : ℝ) / 10000000000 ≤ Real.log ((105819 : ℕ) : ℝ) + (14709 : ℝ) / 10000 := by
  exact endpoint_log_sound 105819 16 130403721186 (by decide +kernel) (by decide +kernel)

private theorem endpoint_072 :
    ((131787790876 : ℕ) : ℝ) / 10000000000 ≤ Real.log ((121526 : ℕ) : ℝ) + (14709 : ℝ) / 10000 := by
  exact endpoint_log_sound 121526 16 131787790876 (by decide +kernel) (by decide +kernel)

private theorem endpoint_073 :
    ((131983841862 : ℕ) : ℝ) / 10000000000 ≤ Real.log ((139546 : ℕ) : ℝ) + (14709 : ℝ) / 10000 := by
  exact endpoint_log_sound 139546 17 131983841862 (by decide +kernel) (by decide +kernel)

private theorem logEndpoints_logBounds : ∀ e ∈ logEndpoints,
    (e.upper : ℝ) / 10000000000 ≤ Real.log (e.lo : ℝ) + (14709 : ℝ) / 10000 := by
  exact List.forall_iff_forall_mem.mp ⟨endpoint_000, endpoint_001, endpoint_002, endpoint_003, endpoint_004, endpoint_005, endpoint_006, endpoint_007, endpoint_008, endpoint_009, endpoint_010, endpoint_011, endpoint_012, endpoint_013, endpoint_014, endpoint_015, endpoint_016, endpoint_017, endpoint_018, endpoint_019, endpoint_020, endpoint_021, endpoint_022, endpoint_023, endpoint_024, endpoint_025, endpoint_026, endpoint_027, endpoint_028, endpoint_029, endpoint_030, endpoint_031, endpoint_032, endpoint_033, endpoint_034, endpoint_035, endpoint_036, endpoint_037, endpoint_038, endpoint_039, endpoint_040, endpoint_041, endpoint_042, endpoint_043, endpoint_044, endpoint_045, endpoint_046, endpoint_047, endpoint_048, endpoint_049, endpoint_050, endpoint_051, endpoint_052, endpoint_053, endpoint_054, endpoint_055, endpoint_056, endpoint_057, endpoint_058, endpoint_059, endpoint_060, endpoint_061, endpoint_062, endpoint_063, endpoint_064, endpoint_065, endpoint_066, endpoint_067, endpoint_068, endpoint_069, endpoint_070, endpoint_071, endpoint_072, endpoint_073⟩

end RamareFiniteBoundsAnalytic


/- Self-contained private component probe.
ArithmeticBridge declarations below are copied unchanged from passed source
414ca09cdd1d926180f1e3dc7777018ecfbc7416a393e952608db29d3735bf64.
No concrete endpoint or prefix table is assumed checked here. -/

open scoped BigOperators

namespace RamareFiniteBoundsAnalytic

/-- Integer reciprocal majorant. Concrete checks must use an efficient,
proved-equal evaluator for totient; this definition is the semantic interface. -/
private theorem one_div_le_rounded_div (D m : ℕ) (hD : 0 < D) (hm : 0 < m) :
    (1 : ℝ) / (m : ℝ) ≤ ((D / m + 1 : ℕ) : ℝ) / (D : ℝ) := by
  have hnat : D < (D / m + 1) * m :=
    (Nat.div_lt_iff_lt_mul hm).mp (Nat.lt_succ_self (D / m))
  have hreal : (D : ℝ) < ((D / m + 1 : ℕ) : ℝ) * (m : ℝ) := by
    exact_mod_cast hnat
  have hDR : (0 : ℝ) < D := by exact_mod_cast hD
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  apply (div_le_div_iff₀ hmR hDR).2
  simpa only [one_mul] using hreal.le

private theorem summand_le_roundedTerm (D n : ℕ) (hD : 0 < D) (hn : 1 ≤ n) :
    (if Squarefree n then (1 : ℝ) / n.totient else 0) ≤
      (roundedTerm D n : ℝ) / (D : ℝ) := by
  by_cases hsq : Squarefree n
  · simp only [roundedTerm, if_pos hsq]
    exact one_div_le_rounded_div D n.totient hD
      (Nat.totient_pos.mpr (Nat.lt_of_lt_of_le Nat.zero_lt_one hn))
  · simp [roundedTerm, hsq]

/-- The natural prefix dominates the exact real sum for every `N`, including zero. -/
private theorem prefix_le_roundedPrefix (D N : ℕ) (hD : 0 < D) :
    (∑ n ∈ Finset.Icc 1 N,
      if Squarefree n then (1 : ℝ) / n.totient else 0) ≤
      (roundedPrefix D N : ℝ) / (D : ℝ) := by
  unfold roundedPrefix
  rw [Nat.cast_sum, Finset.sum_div]
  apply Finset.sum_le_sum
  intro n hn
  exact summand_le_roundedTerm D n hD (Finset.mem_Icc.mp hn).1

private theorem roundedPrefix_mono (D : ℕ) {N M : ℕ} (hNM : N ≤ M) :
    roundedPrefix D N ≤ roundedPrefix D M := by
  unfold roundedPrefix
  apply Finset.sum_le_sum_of_subset
  exact Finset.Icc_subset_Icc le_rfl hNM

/-- A checked upper endpoint controls all smaller positive summation cutoffs. -/
private theorem prefix_le_endpoint (D N b U : ℕ) (hD : 0 < D) (hNb : N ≤ b)
    (hU : roundedPrefix D b ≤ U) :
    (∑ n ∈ Finset.Icc 1 N,
      if Squarefree n then (1 : ℝ) / n.totient else 0) ≤
      (U : ℝ) / (D : ℝ) := by
  refine (prefix_le_roundedPrefix D N hD).trans ?_
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg D)
  exact_mod_cast (roundedPrefix_mono D hNb).trans hU

end RamareFiniteBoundsAnalytic


namespace RamareFiniteBoundsAnalytic

/-- A linear-size coverage certificate for consecutive, nonempty intervals.
The empty tail must start exactly after the declared final endpoint. -/
private def consecutiveCover {α : Type*} (lo hi : α → ℕ) : ℕ → ℕ → List α → Bool
  | next, last, [] => decide (next = last + 1)
  | next, last, r :: rs =>
      decide (lo r = next ∧ lo r ≤ hi r) &&
        consecutiveCover lo hi (hi r + 1) last rs

/-- A successful structural coverage check supplies an actual containing row.
The lower endpoint is at least the initial start, preserving positivity. -/
private theorem consecutiveCover_sound {α : Type*} (lo hi : α → ℕ)
    (rows : List α) (next last N : ℕ)
    (hcover : consecutiveCover lo hi next last rows = true)
    (hnext : next ≤ N) (hlast : N ≤ last) :
    ∃ r ∈ rows, next ≤ lo r ∧ lo r ≤ N ∧ N ≤ hi r := by
  induction rows generalizing next with
  | nil =>
    simp only [consecutiveCover, decide_eq_true_eq] at hcover
    omega
  | cons r rs ih =>
    simp only [consecutiveCover, Bool.and_eq_true, decide_eq_true_eq] at hcover
    rcases hcover with ⟨⟨hlo, hnonempty⟩, htail⟩
    by_cases hNr : N ≤ hi r
    · exact ⟨r, by simp, by omega, by omega, hNr⟩
    · obtain ⟨s, hs, hstart, hloN, hNhi⟩ :=
        ih (hi r + 1) htail (by omega)
      exact ⟨s, by simp [hs], by omega, hloN, hNhi⟩

/-- Assembly only: numerical prefix bounds and logarithm bounds are explicit
obligations. This theorem does not certify any concrete arithmetic table. -/
private theorem finite_bound_of_endpoint_certificates {α : Type*}
    (rows : List α) (lo hi upper : α → ℕ) (D B : ℕ) (C : ℝ)
    (hD : 0 < D)
    (hcover : consecutiveCover lo hi 1 B rows = true)
    (hprefix : ∀ r ∈ rows, roundedPrefix D (hi r) ≤ upper r)
    (hlog : ∀ r ∈ rows, (upper r : ℝ) / (D : ℝ) ≤ Real.log (lo r : ℝ) + C)
    (N : ℕ) (hN1 : 1 ≤ N) (hNB : N ≤ B) :
    (∑ n ∈ Finset.Icc 1 N,
      if Squarefree n then (1 : ℝ) / n.totient else 0) ≤
      Real.log (N : ℝ) + C := by
  obtain ⟨r, hr, hpos, hloN, hNhi⟩ :=
    consecutiveCover_sound lo hi rows 1 B N hcover hN1 hNB
  have hsum := prefix_le_endpoint D N (hi r) (upper r) hD hNhi (hprefix r hr)
  refine hsum.trans ((hlog r hr).trans ?_)
  refine add_le_add ?_ (le_refl C)
  apply Real.log_le_log
  · exact_mod_cast (Nat.lt_of_lt_of_le Nat.zero_lt_one hpos)
  · exact_mod_cast hloN

end RamareFiniteBoundsAnalytic



namespace RamareFiniteBoundsAnalytic

/-- Exactly 74 structural interval checks, without enumerating all N. -/
private theorem logEndpoints_consecutive :
    consecutiveCover LogEndpoint.lo LogEndpoint.hi 1 142300 logEndpoints = true := by
  decide +kernel

/-- Private assembly interface. The substantive arithmetic prefix bounds
are explicit hypotheses; this is not a closed proof of the platform target. -/
private theorem finite_range_of_logEndpoint_prefixes
    (hprefix : ∀ e ∈ logEndpoints, roundedPrefix 10000000000 e.hi ≤ e.upper)
    (N : ℕ) (hN1 : 1 ≤ N) (hN2 : N ≤ 142300) :
    (∑ n ∈ Finset.Icc 1 N,
      if Squarefree n then (1 : ℝ) / Nat.totient n else 0) ≤
      Real.log (N : ℝ) + 1.4709 := by
  have h := finite_bound_of_endpoint_certificates logEndpoints
    LogEndpoint.lo LogEndpoint.hi LogEndpoint.upper 10000000000 142300
    ((14709 : ℝ) / 10000) (by decide +kernel) logEndpoints_consecutive
    hprefix logEndpoints_logBounds N hN1 hN2
  simpa only [show (14709 : ℝ) / 10000 = (1.4709 : ℝ) by norm_num] using h

end RamareFiniteBoundsAnalytic



theorem solution (N : ℕ) (hN1 : 1 ≤ N) (hN2 : N ≤ 142300) :
    (∑ n ∈ Finset.Icc 1 N,
      if Squarefree n then (1 : ℝ) / Nat.totient n else 0) ≤
      Real.log (N : ℝ) + 1.4709 :=
  RamareFiniteBoundsAnalytic.finite_range_of_logEndpoint_prefixes
    (fun e he => (RamareFiniteBounds.endpoint_prefixes e he).le) N hN1 hN2

#print axioms solution
