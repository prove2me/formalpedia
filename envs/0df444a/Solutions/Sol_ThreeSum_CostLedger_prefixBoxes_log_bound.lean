-- Prove2me | solution 1 for ThreeSum.CostLedger.prefixBoxes_log_bound
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-10-14T16:09:44.372973+00:00
-- url     : https://prove2.me/submissions/466a0e06-c3c1-4c88-bb32-16302e5db7bc

import Aesop
import Definitions.Def_ThreeSum1962Source_Bundle01
import Definitions.Def_ThreeSum1962Source_Bundle04
import Definitions.Def_ThreeSum1962Source_Bundle07
import Definitions.Def_ThreeSum1962Source_Bundle08
import Definitions.Def_ThreeSum1962Source_Bundle09
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Floor.Div
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.NthRootLemmas
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Bool.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.List.MinMax
import Mathlib.Data.List.Pi
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.Index
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Matrix.Dual
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.NumberTheory.Bertrand
import Mathlib.NumberTheory.Chebyshev
import Mathlib.Order.Monotone.Basic
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs
import Theorems.Thm_ThreeSum_Switch_actual_switch_certified


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
namespace ThreeSum.Parameters
end ThreeSum.Parameters
namespace ThreeSum.Scales
end ThreeSum.Scales
namespace ThreeSum.Switch
end ThreeSum.Switch

section


/-!
# Analytic and rational parameter certificate for the proposed 3SUM algorithm

This module certifies the real-variable inequalities and the resulting exponent ledger.
It does not by itself prove that an implementation has those costs: the reduction,
cover, encoding, reporting, arithmetic and machine-model lemmas are separate obligations.

All decimal-looking constants below are exact rational numbers. There are no numerical
oracles, admitted declarations, or native-code decision procedures in this certificate.
-/

noncomputable section

namespace ThreeSum.Parameters

open Set Real

set_option maxRecDepth 10000
set_option maxHeartbeats 0
set_option exponentiation.threshold 2048







































/-! ## Exact integer witnesses for the logarithmic comparisons -/































































































































































/-! ## Exact rational inequalities for the schedule -/



theorem phi_half : phi (1 / 2) = (841 / 200 : ℝ) := by norm_num [phi]

























































































































































































































theorem switchThreshold_upper {a : ℝ} (ha : a ∈ Icc (0 : ℝ) terminalFraction) :
    switchThreshold a ≤ 941 / 350 := by
  have hden : 0 < 1 - a := by dsimp [terminalFraction] at ha; linarith [ha.2]
  rw [switchThreshold, div_le_iff₀ hden]
  dsimp [boxSaving, bandShift, terminalFraction] at *
  linarith [ha.2]














































/-! ## The real-valued ledger, before the algorithmic cost lemmas are applied -/





























































end ThreeSum.Parameters

end
end

section


/-!
# The actual integer block schedule

All four size parameters below are executable natural-number functions.
The finite bounds and limits concern these functions, including the even
rounding of the cube root and the divisibility constraints on the number
of blocks.  No asymptotic size premise is imposed on the schedule.
-/

namespace ThreeSum.Scales

open Filter Real
open scoped Topology













































theorem microSize_even (m : ℕ) : 2 ∣ microSize m := by
  exact ⟨Nat.nthRoot 3 m / 2, rfl⟩


































noncomputable section



























































































































































































































































































































































































































































































































































































































































































































































































































































end

end ThreeSum.Scales

end

section


/-!
# The executable integer cubic switch

The implementation scans integers `q ≤ r/2` and tests a cleared integer
inequality.  No real-number comparison, logarithm oracle, or unbounded
noncomputable search occurs in the definition.  For admissible depths the
candidate set is nonempty.  Minimality gives the exact `9/r` rounding error
needed by the certified box and entropy bounds.
-/

namespace ThreeSum.Switch

open Set ThreeSum.Parameters ThreeSum.Scales

set_option maxHeartbeats 0






















@[simp] theorem mem_candidates {J j r q : ℕ} :
    q ∈ candidates J j r ↔ q ≤ r / 2 ∧ accepts J j r q := by
  simp [candidates, Nat.lt_succ_iff]

theorem switchIndex_mem {J j r : ℕ} (h : (candidates J j r).Nonempty) :
    switchIndex J j r ∈ candidates J j r := by
  simp only [switchIndex, dif_pos h]
  exact Finset.min'_mem _ _







noncomputable section

theorem depth_fraction {J j : ℕ} (hJ : 0 < J) (hj : 20 * j ≤ 13 * J) :
    (j : ℝ) / J ∈ Icc (0 : ℝ) terminalFraction := by
  have hJR : (0 : ℝ) < J := by exact_mod_cast hJ
  constructor
  · positivity
  · rw [div_le_iff₀ hJR]
    have ht : (20 : ℝ) * j ≤ 13 * J := by exact_mod_cast hj
    dsimp [terminalFraction]
    linarith

theorem depth_lt {J j : ℕ} (hJ : 0 < J) (hj : 20 * j ≤ 13 * J) : j < J := by
  omega

theorem threshold_fraction {J j : ℕ} (hJ : 0 < J) (hj : j < J) :
    switchThreshold ((j : ℝ) / J) =
      (291 * (J : ℝ) + 1000 * j) / (1000 * ((J - j : ℕ) : ℝ)) := by
  have hJR : (J : ℝ) ≠ 0 := by exact_mod_cast hJ.ne'
  have hd : ((J - j : ℕ) : ℝ) = (J : ℝ) - j := by
    exact Nat.cast_sub hj.le
  have hden : (J : ℝ) - j ≠ 0 := by
    have hlt : (j : ℝ) < J := by exact_mod_cast hj
    linarith
  rw [hd]
  unfold switchThreshold boxSaving bandShift
  field_simp
  <;> ring

theorem phi_fraction {r q : ℕ} (hr : 0 < r) :
    phi ((q : ℝ) / r) = (cubicNumerator r q : ℝ) / (100 * (r : ℝ) ^ 3) := by
  have hrR : (r : ℝ) ≠ 0 := by exact_mod_cast hr.ne'
  simp only [phi, cubicNumerator, Nat.cast_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  field_simp
  <;> ring

theorem accepts_iff {J j r q : ℕ} (hJ : 0 < J) (hj : j < J) (hr : 0 < r) :
    accepts J j r q ↔ switchThreshold ((j : ℝ) / J) ≤ phi ((q : ℝ) / r) := by
  have hd : (0 : ℝ) < ((J - j : ℕ) : ℝ) := by exact_mod_cast Nat.sub_pos_of_lt hj
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  rw [threshold_fraction hJ hj, phi_fraction hr, div_le_div_iff₀ (by positivity) (by positivity)]
  have hc : accepts J j r q ↔
      (291 * (J : ℝ) + 1000 * j) * (r : ℝ) ^ 3 ≤
        10 * ((J - j : ℕ) : ℝ) * (cubicNumerator r q : ℝ) := by
    unfold accepts
    exact_mod_cast Iff.rfl
  rw [hc]
  constructor <;> intro h <;> nlinarith

theorem half_fraction {r : ℕ} (hr : 0 < r) (heven : 2 ∣ r) :
    ((r / 2 : ℕ) : ℝ) / r = (1 / 2 : ℝ) := by
  have hm := Nat.div_mul_cancel heven
  have hmR : ((r / 2 : ℕ) : ℝ) * 2 = r := by exact_mod_cast hm
  have hrR : (r : ℝ) ≠ 0 := by exact_mod_cast hr.ne'
  field_simp
  linarith

theorem candidates_nonempty {J j r : ℕ} (hJ : 0 < J) (hj : 20 * j ≤ 13 * J)
    (hr : 0 < r) (heven : 2 ∣ r) : (candidates J j r).Nonempty := by
  refine ⟨r / 2, mem_candidates.mpr ⟨le_rfl, ?_⟩⟩
  rw [accepts_iff hJ (depth_lt hJ hj) hr, half_fraction hr heven, phi_half]
  have h := switchThreshold_upper (depth_fraction hJ hj)
  linarith

theorem switchIndex_spec {J j r : ℕ} (hJ : 0 < J) (hj : 20 * j ≤ 13 * J)
    (hr : 0 < r) (heven : 2 ∣ r) :
    switchIndex J j r ≤ r / 2 ∧ accepts J j r (switchIndex J j r) :=
  mem_candidates.mp (switchIndex_mem (candidates_nonempty hJ hj hr heven))
































































theorem actual_totalSize (n : ℕ) : mu n = blockCount (inputBits n) * muZero n := rfl

theorem actual_residual_even (n j : ℕ) : 2 ∣ residualSize n j := by
  exact dvd_mul_of_dvd_right (microSize_even (inputBits n)) _

theorem actual_depth_condition {n j : ℕ} (hj : j ≤ terminalDepth n) :
    20 * j ≤ 13 * blockCount (inputBits n) := by
  have hm := Nat.div_mul_le_self (13 * blockCount (inputBits n)) 20
  unfold terminalDepth at hj
  omega

theorem actual_residual_pos {n j : ℕ} (hmu : 0 < mu n) (hj : j ≤ terminalDepth n) :
    0 < residualSize n j := by
  rw [actual_totalSize] at hmu
  have hp := And.intro (Nat.pos_of_mul_pos_right hmu) (Nat.pos_of_mul_pos_left hmu)
  have hd := depth_lt hp.1 (actual_depth_condition hj)
  exact Nat.mul_pos (Nat.sub_pos_of_lt hd) hp.2

theorem residual_real_identity {n j : ℕ} (hmu : 0 < mu n)
    (hj : j ≤ terminalDepth n) :
    (residualSize n j : ℝ) =
      (1 - (j : ℝ) / blockCount (inputBits n)) * mu n := by
  have hm := hmu
  rw [actual_totalSize] at hm
  have hp := And.intro (Nat.pos_of_mul_pos_right hm) (Nat.pos_of_mul_pos_left hm)
  have hlt := depth_lt hp.1 (actual_depth_condition hj)
  have hJ : (blockCount (inputBits n) : ℝ) ≠ 0 := by exact_mod_cast hp.1.ne'
  simp only [residualSize, actual_totalSize, Nat.cast_mul, Nat.cast_sub hlt.le]
  field_simp
  <;> ring








































end
end ThreeSum.Switch

end

section


/-!
# Actual finite hierarchy counts

These are the binomial counts used by the concrete microblock hierarchy.
Every prefix partition is included.  The integer switch and its rounding
allowance are applied before any asymptotic estimate is made.  The counts
in this module are combinatorial work counts; the implementation's operation
counts, raw wanted incidences, and false-mass bounds are separate interfaces.
-/

namespace ThreeSum.CostLedger

open Filter Set Real ThreeSum.Parameters ThreeSum.Scales ThreeSum.Switch
open scoped Topology BigOperators

set_option maxHeartbeats 400000


































theorem microOutputs_pos (n : ℕ) : 0 < microOutputs n :=
  Nat.choose_pos (by omega)

theorem microPartitions_pos (n : ℕ) : 0 < microPartitions n :=
  Nat.choose_pos (Nat.div_le_self _ _)

theorem prefixChoices_pos (n j : ℕ) : 0 < prefixChoices n j :=
  Nat.pow_pos (Nat.mul_pos (microOutputs_pos n) (microPartitions_pos n))

theorem suffixBoxes_pos (n j : ℕ) : 0 < suffixBoxes n j :=
  Nat.choose_pos (by omega)




noncomputable section

theorem microOutputs_log_bound {n : ℕ} (hmu : 0 < mu n) :
    Real.log (microOutputs n : ℝ) ≤ 2 * E * muZero n * Real.log 2 := by
  have hprod := hmu
  rw [actual_totalSize] at hprod
  have hm := Nat.pos_of_mul_pos_left hprod
  have hmR : (0 : ℝ) < muZero n := by exact_mod_cast hm
  have hb := (BinomialEntropy.fixed_ratio_bounds (c := 256) (r := 1)
    (by norm_num) (by norm_num) hm).2
  simp only [Nat.one_mul, Nat.cast_ofNat, Nat.cast_one] at hb
  have hc := (div_le_iff₀ hmR).mp hb
  change Real.log (((256 * muZero n).choose (muZero n) : ℕ) : ℝ) ≤ _
  have hid : 2 * E * (muZero n : ℝ) * Real.log 2 =
      256 * Real.binEntropy (1 / 256) * muZero n := by
    unfold E entropy
    field_simp
    <;> ring
  rw [hid]
  exact hc

theorem microPartitions_log_bound (n : ℕ) :
    Real.log (microPartitions n : ℝ) ≤ (muZero n : ℝ) * Real.log 2 := by
  have hp : (0 : ℝ) < microPartitions n := by exact_mod_cast microPartitions_pos n
  have hb : (microPartitions n : ℝ) ≤ (2 : ℝ) ^ muZero n := by
    exact_mod_cast Nat.choose_le_two_pow (muZero n) (muZero n / 2)
  simpa only [Real.log_pow, Nat.cast_ofNat] using Real.log_le_log hp hb

theorem prefixChoices_log_bound {n j : ℕ} (hmu : 0 < mu n) :
    Real.log (prefixChoices n j : ℝ) ≤
      (j : ℝ) * muZero n * Real.log 2 * (2 * E + 1) := by
  have hM : (microOutputs n : ℝ) ≠ 0 := by exact_mod_cast (microOutputs_pos n).ne'
  have hG : (microPartitions n : ℝ) ≠ 0 := by exact_mod_cast (microPartitions_pos n).ne'
  simp only [prefixChoices, Nat.cast_pow, Nat.cast_mul, Real.log_pow, Real.log_mul hM hG]
  have hsum := add_le_add (microOutputs_log_bound hmu) (microPartitions_log_bound n)
  have hmul := mul_le_mul_of_nonneg_left hsum (Nat.cast_nonneg (α := ℝ) j)
  nlinarith

theorem suffixBoxes_log_bound {n j : ℕ} (hmu : 0 < mu n)
    (hj : j ≤ terminalDepth n) :
    Real.log (suffixBoxes n j : ℝ) ≤
      (residualSize n j : ℝ) * Real.log 2 *
        (2 * E - gamma ((actualSwitch n j : ℝ) / residualSize n j)) := by
  have hr := actual_residual_pos hmu hj
  have hrR : (0 : ℝ) < residualSize n j := by exact_mod_cast hr
  have hprod := hmu
  rw [actual_totalSize] at hprod
  have hspec := switchIndex_spec (Nat.pos_of_mul_pos_right hprod)
    (actual_depth_condition hj) hr (actual_residual_even n j)
  have hq : actualSwitch n j ≤ residualSize n j := by
    unfold actualSwitch
    exact hspec.1.trans (Nat.div_le_self _ _)
  have hb := (BinomialEntropy.log_choose_entropy_bounds
    (show residualSize n j - actualSwitch n j ≤ 256 * residualSize n j by omega)).2
  have hratio : ((residualSize n j - actualSwitch n j : ℕ) : ℝ) /
      ((256 * residualSize n j : ℕ) : ℝ) =
        (1 - (actualSwitch n j : ℝ) / residualSize n j) / 256 := by
    rw [Nat.cast_sub hq, Nat.cast_mul, Nat.cast_ofNat]
    field_simp
    <;> ring
  rw [hratio, Nat.cast_mul, Nat.cast_ofNat] at hb
  have hid : (residualSize n j : ℝ) * Real.log 2 *
      (2 * E - gamma ((actualSwitch n j : ℝ) / residualSize n j)) =
        256 * (residualSize n j : ℝ) *
          Real.binEntropy ((1 - (actualSwitch n j : ℝ) / residualSize n j) / 256) := by
    unfold E gamma entropy
    field_simp
    <;> ring
  rw [hid]
  exact hb

theorem prefixBoxes_log_bound_sourceProof {n j : ℕ} (hmu : 0 < mu n)
    (hj : j ≤ terminalDepth n) :
    Real.log (prefixBoxes n j : ℝ) ≤
      (mu n : ℝ) * Real.log 2 * (2 * E + 2 * bandShift - boxSaving) := by
  have hp : (prefixChoices n j : ℝ) ≠ 0 := by exact_mod_cast (prefixChoices_pos n j).ne'
  have hs : (suffixBoxes n j : ℝ) ≠ 0 := by exact_mod_cast (suffixBoxes_pos n j).ne'
  have hb := add_le_add (prefixChoices_log_bound (j := j) hmu) (suffixBoxes_log_bound hmu hj)
  have hc := (actual_switch_certified hmu hj).2.1
  have hn : (0 : ℝ) ≤ (mu n : ℝ) * Real.log 2 :=
    mul_nonneg (Nat.cast_nonneg _) log_two_pos.le
  have hmul := mul_le_mul_of_nonneg_left hc hn
  have hid := residual_real_identity hmu hj
  have hprod : (mu n : ℝ) = (blockCount (inputBits n) : ℝ) * muZero n := by
    exact_mod_cast actual_totalSize n
  have hpos := hmu
  rw [actual_totalSize] at hpos
  have hJ : (blockCount (inputBits n) : ℝ) ≠ 0 :=
    by exact_mod_cast (Nat.pos_of_mul_pos_right hpos).ne'
  have hjid : (j : ℝ) * muZero n =
      ((j : ℝ) / blockCount (inputBits n)) * mu n := by rw [hprod]; field_simp
  have hcombine : (j : ℝ) * muZero n * Real.log 2 * (2 * E + 1) +
      (residualSize n j : ℝ) * Real.log 2 *
        (2 * E - gamma ((actualSwitch n j : ℝ) / residualSize n j)) =
      (mu n : ℝ) * Real.log 2 *
        (2 * E + (j : ℝ) / blockCount (inputBits n) -
          (1 - (j : ℝ) / blockCount (inputBits n)) *
            gamma ((actualSwitch n j : ℝ) / residualSize n j)) := by
    rw [hjid, hid]
    ring
  rw [hcombine] at hb
  simp only [prefixBoxes, Nat.cast_mul, Real.log_mul hp hs]
  linear_combination hb + hmul











































end
end ThreeSum.CostLedger

end


theorem solution : ∀ {n j : Nat},
  @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (ThreeSum.Scales.mu n) →
    @LE.le.{0} Nat instLENat j (ThreeSum.Switch.terminalDepth n) →
      @LE.le.{0} Real Real.instLE (Real.log (@Nat.cast.{0} Real Real.instNatCast (ThreeSum.CostLedger.prefixBoxes n j)))
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
            (@Nat.cast.{0} Real Real.instNatCast (ThreeSum.Scales.mu n))
            (Real.log
              (@OfNat.ofNat.{0} Real (nat_lit 2)
                (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                  (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                    (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))))
          (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
            (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
              (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                (@OfNat.ofNat.{0} Real (nat_lit 2)
                  (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                    (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                      (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
                ThreeSum.Parameters.E)
              (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                (@OfNat.ofNat.{0} Real (nat_lit 2)
                  (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                    (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                      (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
                ThreeSum.Parameters.bandShift))
            ThreeSum.Parameters.boxSaving)) := by
  exact @ThreeSum.CostLedger.prefixBoxes_log_bound_sourceProof

#print axioms solution
