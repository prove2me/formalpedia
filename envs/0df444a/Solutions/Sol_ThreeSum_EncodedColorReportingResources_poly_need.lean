-- Prove2me | solution 1 for ThreeSum.EncodedColorReportingResources.poly_need
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-10-14T16:35:23.718513+00:00
-- url     : https://prove2.me/submissions/8881fcb7-355e-43ba-8801-c86e83f85104

/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

import Aesop
import Definitions.Def_APSPSource_RemainingDefinitions
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Logic
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Regions
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_WordSize
import Definitions.Def_ThreeSum1962Source_Bundle01
import Definitions.Def_ThreeSum1962Source_Bundle02
import Definitions.Def_ThreeSum1962Source_Bundle03
import Definitions.Def_ThreeSum1962Source_Bundle05
import Definitions.Def_ThreeSum1962Source_Bundle06
import Definitions.Def_ThreeSum1962Source_Bundle07
import Definitions.Def_ThreeSum1962Source_Bundle08
import Definitions.Def_ThreeSum1962Source_Bundle09
import Definitions.Def_ThreeSum1962Source_Bundle10
import Definitions.Def_ThreeSum1962Source_Bundle11
import Definitions.Def_ThreeSum1962Source_Bundle12
import Definitions.Def_ThreeSum1962Source_Bundle13
import Definitions.Def_ThreeSum1962Source_Bundle14
import Definitions.Def_ThreeSum1962Source_Bundle15
import Definitions.Def_ThreeSum1962Source_Bundle16
import Definitions.Def_ThreeSum1962Source_Bundle17
import Definitions.Def_TrulySubcubicAPSP_SourceSpecification
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.GCDMonoid.Nat
import Mathlib.Algebra.Group.Equiv.Basic
import Mathlib.Algebra.Group.Int.Defs
import Mathlib.Algebra.GroupWithZero.Nat
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Algebra.Order.BigOperators.Group.Multiset
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.List
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Floor.Div
import Mathlib.Algebra.Order.Group.Abs
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Algebra.Order.Group.Nat
import Mathlib.Algebra.Order.Group.Unbundled.Abs
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Algebra.Ring.Nat
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.NthRootLemmas
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Combinatorics.Colex
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Bool.Basic
import Mathlib.Data.Fin.Embedding
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Image
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Range
import Mathlib.Data.Finset.Sigma
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Fin
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sets
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Int.Basic
import Mathlib.Data.Int.Cast.Lemmas
import Mathlib.Data.Int.ModEq
import Mathlib.Data.Int.Notation
import Mathlib.Data.Int.SuccPred
import Mathlib.Data.List.Basic
import Mathlib.Data.List.Dedup
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.GetD
import Mathlib.Data.List.MinMax
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.OfFn
import Mathlib.Data.List.Pi
import Mathlib.Data.List.ProdSigma
import Mathlib.Data.List.Range
import Mathlib.Data.List.Sublists
import Mathlib.Data.List.TakeDrop
import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.Nat.Cast.Order.Ring
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Choose.Vandermonde
import Mathlib.Data.Nat.Count
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Size
import Mathlib.Data.Nat.Sqrt
import Mathlib.Data.Nat.SuccPred
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.Index
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.LinearAlgebra.Matrix.Dual
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Logic.Function.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.NumberTheory.Bertrand
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Order.Monotone.Basic
import Mathlib.Probability.Independence.Basic
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Tactic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.DeriveFintype
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.Tauto
import Theorems.Thm_ThreeSum_EncodedColorResources_dimensions
import Theorems.Thm_ThreeSum_EncodedColorResources_prime_word_bound
import Theorems.Thm_ThreeSum_EncodedColorResources_source_word_bound
import Theorems.Thm_ThreeSum_EncodedColorResources_stage_depth_bound
import Theorems.Thm_ThreeSum_KaratsubaInterface_capacity_lt_twice
import Theorems.Thm_ThreeSum_LightLocalCoverMagnitude_bounds
import Theorems.Thm_ThreeSum_LightLocalCoverResources_word_polynomial
import Theorems.Thm_ThreeSum_LocalParameterBounds_count_word_bound
import Theorems.Thm_ThreeSum_PolynomialResources_pair_polyBound_of_powerBound
import Theorems.Thm_ThreeSum_Scales_natSqrt_ratio_tendsto_zero
import Theorems.Thm_ThreeSum_SharedReportingBankResourceBounds_components
import Theorems.Thm_ThreeSum_StageBounds_PowerBound_add_same
import Theorems.Thm_ThreeSum_ThreeSumReportingSetupResources_poly_need


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
namespace Light
end Light
namespace ThreeSum.ArithmeticStageBounds
end ThreeSum.ArithmeticStageBounds
namespace ThreeSum.BandScales
end ThreeSum.BandScales
namespace ThreeSum.CostLedger
end ThreeSum.CostLedger
namespace ThreeSum.EncodedColorLayout
end ThreeSum.EncodedColorLayout
namespace ThreeSum.GlobalEncoding
end ThreeSum.GlobalEncoding
namespace ThreeSum.HierarchyScales
end ThreeSum.HierarchyScales
namespace ThreeSum.KaratsubaInterface
end ThreeSum.KaratsubaInterface
namespace ThreeSum.LightLocalCoverLayout
end ThreeSum.LightLocalCoverLayout
namespace ThreeSum.LightLocalCoverMagnitude
end ThreeSum.LightLocalCoverMagnitude
namespace ThreeSum.LightLocalCoverSchedule
end ThreeSum.LightLocalCoverSchedule
namespace ThreeSum.LightLocalCoverTables
end ThreeSum.LightLocalCoverTables
namespace ThreeSum.LocalCoverBounds
end ThreeSum.LocalCoverBounds
namespace ThreeSum.MassScales
end ThreeSum.MassScales
namespace ThreeSum.ModuloCosts
end ThreeSum.ModuloCosts
namespace ThreeSum.Parameters
end ThreeSum.Parameters
namespace ThreeSum.Scales
end ThreeSum.Scales
namespace ThreeSum.StageBounds
end ThreeSum.StageBounds
namespace ThreeSum.Switch
end ThreeSum.Switch
namespace ThreeSum.ThreeSumReportingSetupData
end ThreeSum.ThreeSumReportingSetupData
namespace ThreeSum.TrimScales
end ThreeSum.TrimScales
namespace ThreeSum.UniformStageBounds
end ThreeSum.UniformStageBounds
namespace ThreeSumApsp.WordRam
end ThreeSumApsp.WordRam

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

















































































noncomputable section

















































































































theorem muZero_square_log_ratio_tendsto_zero :
    Tendsto (fun n : ℕ => (muZero n : ℝ) ^ 2 / Real.log n) atTop (𝓝 0) := by
  have h := (microSize_square_ratio_tendsto_zero.comp inputBits_tendsto_atTop).mul
    inputBits_log_ratio_tendsto
  simp only [zero_mul] at h
  apply h.congr'
  filter_upwards [inputBits_tendsto_atTop.eventually (eventually_ge_atTop 1)] with n hn
  have hn0 : (inputBits n : ℝ) ≠ 0 := by exact_mod_cast (by omega : inputBits n ≠ 0)
  simp only [Function.comp_def, muZero]
  field_simp


























































theorem localSearch_log_ratio_tendsto_zero (C : ℕ) :
    Tendsto (fun n : ℕ => Real.log (localSearch C n : ℝ) / Real.log n) atTop (𝓝 0) := by
  have h := muZero_square_log_ratio_tendsto_zero.const_mul ((C : ℝ) * Real.log 2)
  simpa [localSearch, Nat.cast_pow, Nat.cast_mul, Real.log_pow, mul_div_assoc,
    mul_comm, mul_left_comm, mul_assoc] using h

















/-- Converts a proved logarithmic rate into a power bound; the concrete
table and construction functions are instantiated immediately below. -/
theorem eventually_le_rpow_of_log_ratio {f : ℕ → ℕ} {a d : ℝ}
    (hf : Tendsto (fun n : ℕ => Real.log (f n : ℝ) / Real.log n) atTop (𝓝 a))
    (hd : 0 < d) :
    ∀ᶠ n : ℕ in atTop, (f n : ℝ) ≤ (n : ℝ) ^ (a + d) := by
  have hs := hf.eventually (gt_mem_nhds (by linarith : a < a + d))
  filter_upwards [hs, eventually_ge_atTop (2 : ℕ)] with n hn hge
  have hnp : (1 : ℝ) < n := by exact_mod_cast (by omega : 1 < n)
  have hlog : 0 < Real.log n := Real.log_pos hnp
  exact Real.le_rpow_of_log_le (by linarith) ((div_lt_iff₀ hlog).mp hn).le

theorem localSearch_subpolynomial (C : ℕ) {d : ℝ} (hd : 0 < d) :
    ∀ᶠ n : ℕ in atTop, (localSearch C n : ℝ) ≤ (n : ℝ) ^ d := by
  simpa using eventually_le_rpow_of_log_ratio (localSearch_log_ratio_tendsto_zero C) hd































theorem windowExponent_ratio_tendsto_zero :
    Tendsto (fun m : ℕ => (windowExponent m : ℝ) / m) atTop (𝓝 0) := by
  have h := natSqrt_ratio_tendsto_zero.add
    (tendsto_natCast_atTop_atTop (R := ℝ)).inv_tendsto_atTop
  simpa [windowExponent, Nat.cast_add, add_div, one_div] using h

















theorem primeWindow_log_ratio_tendsto_zero :
    Tendsto (fun n : ℕ => Real.log (primeWindow n : ℝ) / Real.log n) atTop (𝓝 0) := by
  have h := ((windowExponent_ratio_tendsto_zero.comp inputBits_tendsto_atTop).mul
    inputBits_log_ratio_tendsto).const_mul (Real.log 2)
  simp only [zero_mul, mul_zero] at h
  apply h.congr'
  filter_upwards [inputBits_tendsto_atTop.eventually (eventually_ge_atTop 1)] with n hn
  have hn0 : (inputBits n : ℝ) ≠ 0 := by exact_mod_cast (by omega : inputBits n ≠ 0)
  simp only [Function.comp_def, primeWindow, Nat.cast_pow, Real.log_pow, Nat.cast_ofNat]
  field_simp






















































theorem muZero_eq_twice_half (n : ℕ) : muZero n = 2 * microHalf (inputBits n) := rfl











































































































































































































































































































































































































































































































end

end ThreeSum.Scales

end

section


/-!
# Actual wanted-incidence and false-mass majorants

The numerator of the wanted bound retains all raw A occurrences, all three
arithmetic lifts, and every schedule occurrence.  The false bound uses the
actual candidate count, integer band count, score loss, and modulus loss.
No asymptotic premise about an input-dependent mass is assumed here: the
transfer lemmas take the explicit finite inequalities from the counting
and prime-chain algorithms.
-/

namespace ThreeSum.MassScales

open Filter Real ThreeSum.Parameters ThreeSum.Scales ThreeSum.TrimScales
  ThreeSum.BandScales ThreeSum.CostLedger ThreeSum.HierarchyScales
open scoped Topology

set_option maxHeartbeats 1000000
set_option maxRecDepth 10000



















































noncomputable section





theorem nat_log_rate_const (c : ℕ) :
    Tendsto (fun n : ℕ => Real.log (c : ℝ) / Real.log n) atTop (𝓝 0) := by
  simpa only [mul_zero, Pi.inv_apply, div_eq_mul_inv] using
    Asymptotics.log_nat_tendsto_atTop.inv_tendsto_atTop.const_mul (Real.log (c : ℝ))




















































































































































end
end ThreeSum.MassScales

end

section


/-!
# The six principal finite stage counts

This module assembles actual natural-number work quantities.  Its final
theorem is a runtime-ledger target, not a 3SUM correctness or machine-time
theorem.  The only input-dependent assumptions are four explicit finite
counting inequalities for the wanted mass and the prime-chain score.
An implementation must still connect its operation counter to these counts.
-/

namespace ThreeSum.StageBounds

open Filter Real ThreeSum.Parameters ThreeSum.Scales ThreeSum.TrimScales
  ThreeSum.BandScales ThreeSum.Switch ThreeSum.CostLedger ThreeSum.HierarchyScales
  ThreeSum.MassScales
open scoped Topology

set_option maxHeartbeats 1000000
set_option maxRecDepth 10000


























noncomputable section





namespace PowerBound

theorem of_rate {f : ℕ → ℕ} {a : ℝ}
    (hf : Tendsto (fun n : ℕ => Real.log (f n : ℝ) / Real.log n) atTop (𝓝 a)) : PowerBound f a :=
  fun _ hd => eventually_le_rpow_of_log_ratio hf hd

theorem const (c : ℕ) : PowerBound (fun _ => c) 0 := of_rate (nat_log_rate_const c)

theorem mul {f g : ℕ → ℕ} {a b : ℝ} (hf : PowerBound f a) (hg : PowerBound g b) :
    PowerBound (fun n => f n * g n) (a + b) := by
  intro d hd
  filter_upwards [hf (d / 2) (by linarith), hg (d / 2) (by linarith),
    eventually_ge_atTop (1 : ℕ)] with n hfn hgn hn
  have hnR : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  rw [Nat.cast_mul]
  calc
    _ ≤ (n : ℝ) ^ (a + d / 2) * (n : ℝ) ^ (b + d / 2) :=
      mul_le_mul hfn hgn (Nat.cast_nonneg _) (Real.rpow_nonneg hnR.le _)
    _ = (n : ℝ) ^ ((a + b) + d) := by rw [← Real.rpow_add hnR]; congr 1; ring

theorem mono_exponent {f : ℕ → ℕ} {a b : ℝ} (hf : PowerBound f a) (hab : a ≤ b) :
    PowerBound f b := by
  intro d hd
  filter_upwards [hf d hd, eventually_ge_atTop (1 : ℕ)] with n hn hge
  exact hn.trans (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hge) (by linarith))















theorem pow {f : ℕ → ℕ} {a : ℝ} (hf : PowerBound f a) (k : ℕ) :
    PowerBound (fun n => f n ^ k) ((k : ℝ) * a) := by
  induction k with
  | zero => simpa only [Nat.cast_zero, zero_mul, pow_zero] using const 1
  | succ k ih =>
      simpa only [Nat.pow_succ, Nat.cast_add, Nat.cast_one, add_mul, one_mul] using ih.mul hf

end PowerBound










































































































































































end
end ThreeSum.StageBounds

end

section


/-!
# The arithmetic and balancing work outside the six reporting stages

The finite bounds here include complete modular-counting invocations, their
signed-remainder bit cost, and the actual correlation/minimum routine. They
augment the six-stage reporting budget. The whole solver still has to charge
its actual host operations to this combined budget.
-/

namespace ThreeSum.ArithmeticStageBounds

open Filter Real Parameters Scales BandScales CostLedger HierarchyScales
  MassScales StageBounds UniformStageBounds ModuloCosts
open scoped Topology

set_option maxHeartbeats 1000000




















































noncomputable section

theorem powerBound_mono {f g : ℕ → ℕ} {a : ℝ} (hg : PowerBound g a)
    (hfg : ∀ᶠ n : ℕ in atTop, f n ≤ g n) : PowerBound f a := by
  intro d hd
  filter_upwards [hg d hd, hfg] with n hn hm
  exact (show (f n : ℝ) ≤ (g n : ℝ) by exact_mod_cast hm).trans hn



























theorem window_powerBound : PowerBound primeWindow 0 :=
  PowerBound.of_rate primeWindow_log_ratio_tendsto_zero

theorem maxMod_powerBound : PowerBound maxMod ((E+1/2)/5) := by
  change PowerBound (fun n => radix n*(4*primeWindow n)^2) ((E+1/2)/5)
  have hwindow := ((PowerBound.const 4).mul window_powerBound).pow 2
  have hh := (PowerBound.of_rate radix_log_ratio_tendsto).mul hwindow
  simpa only [zero_add, mul_zero, add_zero] using hh
























































theorem identity_powerBound : PowerBound (fun n : ℕ => n) 1 := by
  intro d hd
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  simpa only [Real.rpow_one] using
    (Real.rpow_le_rpow_of_exponent_le hnR (show (1 : ℝ) ≤ 1+d by linarith))



























end
end ThreeSum.ArithmeticStageBounds

end

section


/-!
# Consecutive bands of a strictly increasing array

The last band is truncated. Every input position belongs to its quotient
band, the bands are strictly separated, and each band has at most `g` entries.
The quotient in these specifications is realized by `LightBandPartition`.
-/

namespace ThreeSum.BandPartition





theorem size_le (n g : ℕ) : size n g ≤ n := by
  unfold size
  split_ifs with h
  · omega
  · have hdiv := Nat.div_le_self (n-1) g
    omega
































































































end ThreeSum.BandPartition

end

section


/-!
# A polynomial bound in the parameters fits in a word

The running-time claims hold at every word size W ≥ b (log₂ p₁ + ⋯ + log₂ p_r + 1), where p₁, …, p_r
are the parameters of the instance and the slope b is chosen with the program (`Admissible`).  A
light program states its limits as a polynomial in the parameters,
`polyBound s k params` = 2^s ((p₁ + 1) ⋯ (p_r + 1))^k.

The main fact is `polyBound_le`: this bound is at most 2^W as soon as b ≥ s + k r + k.  Each factor
p + 1 is at most 2^(log₂ p + 1) (`prod_succ_le`), so with S the sum of the logarithms the bound is
at most 2^(s + k (S + r)), and s + k (S + r) ≤ (s + k r + k) (S + 1) ≤ W.
-/

@[expose] public section

namespace Light

open ThreeSumApsp.WordRam













































/-- The bound grows with its two exponents. -/
theorem polyBound_mono {s s' k k' : ℕ} (hs : s ≤ s') (hk : k ≤ k') (params : List ℕ) :
    polyBound s k params ≤ polyBound s' k' params := by
  have : 0 < (params.map (· + 1)).prod := List.prod_pos (by simp)
  exact Nat.mul_le_mul (Nat.pow_le_pow_right (by norm_num) hs) (Nat.pow_le_pow_right this hk)




































end Light

end
end

section


/-!
# Actual initialization of the integer block schedule

The fixed program computes all initial size parameters from the input
length. It uses the benchmark's proved logarithm, ceiling cube-root and
ceiling-half loops, with exact rounding bridges below. Division is used
only through an actual counting routine on the logarithmic numerator.
-/

namespace ThreeSum.LightScales

open Light ThreeSum.Scales

variable {lim : Limits} {P : Program}

theorem inputBits_le_self (n : ℕ) : inputBits n ≤ n := by
  simpa [inputBits,Nat.log2_eq_log_two] using Nat.log_le_self 2 n















































































































































































end ThreeSum.LightScales

end

section


/-!
# Exact resource formulas for the original-input band and incidence program

These formulas use the existing selected-color layout without changing any
address or procedure. The physical BC, AB, AC owner records and the packed
value, owner, and sorted-position arrays are all included in the extent.
-/

namespace ThreeSum.LightBandRawAResources

open Light EncodedColorLayout

set_option maxHeartbeats 1800000
set_option maxRecDepth 12000



















theorem clog_le_self (n : ℕ) : Nat.clog 2 n ≤ n :=
  Nat.clog_le_of_le_pow (Nat.le_of_lt Nat.lt_two_pow_self)

theorem count_le (n g : ℕ) : ColorBandBounds.count n g ≤ 3*n^2 :=
  Nat.mul_le_mul_left 3 (Nat.pow_le_pow_left (BandPartition.size_le n g) 2)

theorem width_le (n g : ℕ) : ColorBandBounds.width n g ≤ 3*n+1 := by
  have hm := BandPartition.size_le n g
  have hc := clog_le_self (BandPartition.size n g+BandPartition.size n g+BandPartition.size n g+1)
  unfold ColorBandBounds.width LightBandEnumeration.width
  omega










theorem depth_le (W n g : ℕ) : LightBandRawAColor.depth W n g ≤ W+5*n+21 := by
  have hc := clog_le_self n
  have hw := width_le n g
  unfold LightBandRawAColor.depth LightColorBands.depth ColorBandBounds.depth
  omega

end ThreeSum.LightBandRawAResources

end

section


/-!
# From proved resource envelopes to the compiler's polynomial limits

An eventual power bound supplies a single polynomial valid at every input
size, by explicitly absorbing its finitely many exceptions. Multiplying
by a fixed power of the input magnitude then gives the exact two-parameter
`Light.PolyNeed` required by the verified compiler. These lemmas do not
supply resource envelopes for an algorithm; callers must prove those.
-/

namespace ThreeSum.PolynomialResources

open StageBounds Filter Real
open scoped Topology

noncomputable section










































theorem polyNeed_of_envelope {need : ℕ → ℕ → Light.Need} {f : ℕ → ℕ} {a : ℝ}
    (hf : PowerBound f a) (e : ℕ)
    (hword : ∀ n U, (need n U).word ≤ f n*(U+1)^e)
    (hcells : ∀ n U, (need n U).cells ≤ f n*(U+1)^e)
    (hdepth : ∀ n U, (need n U).depth ≤ f n*(U+1)^e) : Light.PolyNeed need := by
  obtain ⟨s,k,h⟩ := pair_polyBound_of_powerBound hf e
  exact ⟨s,k,fun n U => ⟨(hword n U).trans (h n U),
    (hcells n U).trans (h n U),(hdepth n U).trans (h n U)⟩⟩
















end
end ThreeSum.PolynomialResources

end

section


/-!
# Local parameter construction fits the uniform subpolynomial budget

These bounds apply to the actual operational contracts, including the
primality scans and integer division. The deliberately loose envelope is
only used for a microblock whose half-size is a cube root of `log n`.
-/

namespace ThreeSum.LocalParameterBounds

open LocalCoverBounds

set_option maxHeartbeats 1000000




theorem pow_pos (e : ℕ) : 1 ≤ (2 : ℕ)^e := Nat.pos_iff_ne_zero.mpr (pow_ne_zero _ (by decide))

theorem threshold_bound (h : ℕ) : localThreshold h ≤ 2^(514*h) := by
  calc
    localThreshold h ≤ 2^(512*h)*2^(2*h) :=
      Nat.mul_le_mul_right _ (Nat.choose_le_two_pow _ _)
    _ = 2^(514*h) := by rw [← pow_add]; congr 1 <;> omega

theorem vertex_bound (h : ℕ) : vertexCount (512*h) h ≤ 2^(514*h) :=
  (Nat.choose_le_two_pow _ _).trans (Nat.pow_le_pow_right (by decide) (by omega))

theorem root_bound (h : ℕ) : rootCeiling (localThreshold h) ≤ 2*2^(514*h) := by
  have hs := Nat.sqrt_le_self (localThreshold h-1)
  have ht := threshold_bound h
  have hp := pow_pos (514*h)
  unfold rootCeiling
  omega

theorem prime_bound (h : ℕ) : localPrime h ≤ 2^(514*h+2) := by
  have hp := (selectedPrime_spec (localThreshold h)).2.2
  have hr := root_bound h
  change localPrime h ≤ _ at hp
  rw [pow_add]
  norm_num
  omega








































































theorem selected_word_bound (h : ℕ) :
    LightSelectedPrime.word (localThreshold h) ≤ 2^(514*h+8) := by
  have ht := threshold_bound h
  have hx := pow_pos (514*h)
  unfold LightSelectedPrime.word
  rw [pow_add]
  norm_num
  omega

theorem cap_word_bound (h : ℕ) :
    20*(localPrime h+vertexCount (512*h) h+1) ≤ 2^(514*h+7) := by
  have hp := prime_bound h
  have hv := vertex_bound h
  have hx := pow_pos (514*h)
  rw [pow_add] at hp
  norm_num at hp
  rw [pow_add]
  norm_num
  omega

theorem word_bound (h : ℕ) : LightLocalParameters.word h ≤ envelope h := by
  have hc : LightLocalCounts.word h ≤ base h :=
    (count_word_bound h).trans (Nat.pow_le_pow_right (by decide) (by omega))
  have hp : LightSelectedPrime.word (localThreshold h) ≤ base h :=
    (selected_word_bound h).trans (Nat.pow_le_pow_right (by decide) (by omega))
  have hd : 20*(localPrime h+vertexCount (512*h) h+1) ≤ base h :=
    (cap_word_bound h).trans (Nat.pow_le_pow_right (by decide) (by omega))
  have he : envelope h = 4*base h := by unfold envelope base; rw [pow_add]; norm_num; omega
  unfold LightLocalParameters.word
  rw [he]
  omega


















































end ThreeSum.LocalParameterBounds

end

section


/-!
# Polynomial limits for the actual shared reporting host

The finite word, cell, and depth formulas are bounded at every input size.
The resulting `Need` includes the complete executed host, while its time
bound remains the exact shared-box budget proved separately.
-/

namespace ThreeSum.SharedReportingBankResourceBounds

open Scales StageBounds Filter Light
open scoped Topology

set_option maxHeartbeats 1200000
set_option maxRecDepth 14000

noncomputable section

theorem bits_power_powerBound : PowerBound (fun n => 2^(inputBits n)) 1 := by
  apply ArithmeticStageBounds.powerBound_mono ArithmeticStageBounds.identity_powerBound
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
  simpa only [inputBits,Nat.log2_eq_log_two] using
    Nat.pow_log_le_self 2 (by omega : n ≠ 0)

theorem magnitude_powerBound : PowerBound magnitude 2048 := by
  have hh := (PowerBound.const (2^2048)).mul (bits_power_powerBound.pow 2048)
  have he : magnitude = fun n => 2^2048*(2^(inputBits n))^2048 := by
    funext n
    unfold magnitude
    rw [show 2048*(inputBits n+1)=2048+inputBits n*2048 by omega,pow_add,pow_mul]
  rw [he]
  simpa only [Nat.cast_ofNat,mul_one,zero_add] using hh













































end
end ThreeSum.SharedReportingBankResourceBounds

end

section


/-!
# The complete local-cover program fits the uniform local-search budget

Every bound below is for the actual fixed program, including mask and
coefficient construction, counting division, histograms, matrix assembly,
the original greedy loop, and selected-row gathering.
-/

namespace ThreeSum.LightLocalCoverResources

open Light LocalCoverBounds GlobalEncoding LightLocalCoverSchedule LightLocalCoverTables
open LightLocalCoverLayout LightLocalCoverMagnitude

set_option maxHeartbeats 1800000








































































































































theorem word_bound (h : ℕ) : LightLocalCoverSetup.word h ≤ envelope h := by
  have hs : 1 ≤ (h+1)^2 := Nat.pow_pos (by omega)
  calc
    _ ≤ 2000*(magnitude h)^2 := word_polynomial (bounds h)
    _ ≤ 2^11*(magnitude h)^2 := Nat.mul_le_mul_right _ (by decide)
    _ = 2^(11+600000*(h+1)^2*2) := by rw [magnitude,← pow_mul,← pow_add]
    _ ≤ envelope h := Nat.pow_le_pow_right (by decide) (by omega)






























































end ThreeSum.LightLocalCoverResources

end

section


/-! # Resource bounds for the complete h-and-free local-cover initializer -/

namespace ThreeSum.LightLocalCoverInitResources

open Light LocalCoverBounds GlobalEncoding LightLocalCoverSchedule LightLocalCoverTables
open LightLocalCoverLayout

set_option maxHeartbeats 1500000



theorem parameters_envelope_le (h : ℕ) :
    LocalParameterBounds.envelope h ≤ LightLocalCoverResources.envelope h := by
  unfold LocalParameterBounds.envelope LightLocalCoverResources.envelope
  apply Nat.pow_le_pow_right (by decide)
  nlinarith only [Nat.zero_le (h*h)]






theorem four_envelope_le (h : ℕ) :
    4*LightLocalCoverResources.envelope h ≤ envelope h := by
  have hs : 1 ≤ (h+1)^2 := Nat.pow_pos (by omega)
  calc
    _ = 2^2*2^(4000000*(h+1)^2) := rfl
    _ = 2^(2+4000000*(h+1)^2) := (pow_add _ _ _).symm
    _ ≤ envelope h := Nat.pow_le_pow_right (by decide) (by omega)
















theorem word_bound (h : ℕ) : LightLocalCoverInit.word h ≤ envelope h := by
  have hp := (LocalParameterBounds.word_bound h).trans (parameters_envelope_le h)
  have hc := LightLocalCoverResources.word_bound h
  apply (show LightLocalCoverInit.word h ≤ 4*LightLocalCoverResources.envelope h from ?_).trans
    (four_envelope_le h)
  unfold LightLocalCoverInit.word
  omega
















theorem envelope_le_search {n : ℕ} (hh : 1 ≤ Scales.microHalf (Scales.inputBits n)) :
    envelope (Scales.microHalf (Scales.inputBits n)) ≤ Scales.localSearch 5000000 n := by
  unfold envelope Scales.localSearch
  rw [Scales.muZero_eq_twice_half]
  apply Nat.pow_le_pow_right (by decide)
  apply Nat.mul_le_mul_left
  apply Nat.pow_le_pow_left
  omega


























































end ThreeSum.LightLocalCoverInitResources

end

section


/-! # A proved polynomial scale for the selected-color program's dimensions -/

namespace ThreeSum.EncodedColorResources

open Scales BandScales ArithmeticStageBounds StageBounds GlobalEncoding LocalCoverBounds
open Filter

set_option maxHeartbeats 2200000
set_option maxRecDepth 13000








theorem scale_bounds (n : ℕ) : 100 ≤ scale n ∧ n+1 ≤ scale n ∧
    SharedReportingBankResourceBounds.magnitude n ≤ scale n ∧ localEnvelope n ≤ scale n ∧
    maxMod n ≤ scale n ∧ primeWindow n ≤ scale n := by
  unfold scale
  omega

theorem local_bounds (n : ℕ) : LightLocalCoverMagnitude.Bounds (half n) (scale n) := by
  have hm : LightLocalCoverMagnitude.magnitude (half n) ≤ localEnvelope n := by
    unfold LightLocalCoverMagnitude.magnitude localEnvelope LightLocalCoverInitResources.envelope
    exact Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_right _ (by decide : 600000 ≤ 5000000))
  have hs := hm.trans (scale_bounds n).2.2.2.1
  have H := LightLocalCoverMagnitude.bounds (half n)
  exact ⟨H.positive.trans hs,H.width.trans hs,H.vertices.trans hs,H.prime.trans hs,
    H.cap.trans hs,H.candidates.trans hs,H.rounds.trans hs,H.decodePower.trans hs,H.maskPower.trans hs⟩

















theorem powers (n : ℕ) : 2^(width n+1) ≤ scale n ∧
    LightBlockSourceCatalog.count (half n) (blocks n) ≤ scale n ∧
    localPrime (half n)^(blocks n)*localPrime (half n) ≤ scale n ∧
    2^(blocks n) ≤ scale n := by
  have H := SharedReportingBankResourceBounds.components n
  have hm := (scale_bounds n).2.2.1
  refine ⟨H.widthPower.trans hm,H.occurrence.trans hm,H.primePower.trans hm,?_⟩
  have htwo : (2 : ℕ) ≤ 2^(512*half n)+1 := by have hh := Nat.two_pow_pos (512*half n); omega
  exact (Nat.pow_le_pow_left htwo (blocks n)).trans (H.radixPower.trans hm)

theorem modulus_le (n : ℕ) : BlockSourceEncoding.modulus (half n) (blocks n) ≤ scale n := by
  exact (Nat.le_mul_of_pos_right _ (localPrime_pos (half n))).trans (powers n).2.2.1






theorem radix_power_le (n : ℕ) : (localPrime (half n)+1)^(blocks n) ≤ (scale n)^2 := by
  have hp := localPrime_pos (half n)
  have hmod := modulus_le n
  calc
    _ ≤ (2*localPrime (half n))^(blocks n) := Nat.pow_le_pow_left (by omega) _
    _ = 2^(blocks n)*localPrime (half n)^(blocks n) := mul_pow _ _ _
    _ ≤ scale n*scale n := Nat.mul_le_mul (powers n).2.2.2 hmod
    _ = _ := by ring



















theorem totalKeys_le (n : ℕ) : LightGuardedWanted.totalKeys (half n) (blocks n) ≤ (scale n)^2 := by
  have hq : outputCount (512*half n) (half n)^(blocks n) ≤ scale n := by
    calc
      _ ≤ (2^(512*half n))^(blocks n) := Nat.pow_le_pow_left (Nat.choose_le_two_pow _ _) _
      _ = 2^(width n) := by unfold width; rw [← pow_mul]; congr 1; ring
      _ ≤ 2^(width n+1) := Nat.pow_le_pow_right (by decide) (by omega)
      _ ≤ scale n := (powers n).1
  unfold LightGuardedWanted.totalKeys LightGlobalKeys.localCount
  rw [mul_pow]
  exact (Nat.mul_le_mul (powers n).2.1 hq).trans_eq (pow_two _).symm

theorem keyBound_le (n : ℕ) : LightGuardedWanted.keyBound (maxMod n) (half n) (blocks n) ≤ 3*(scale n)^4 := by
  have hP := (scale_bounds n).2.2.2.2.1
  have hL : 512*half n ≤ scale n := by have h := (local_bounds n).width; omega
  have hp : localPrime (half n) ≤ scale n := by have h := (local_bounds n).prime; omega
  have hm := Nat.mul_le_mul (Nat.mul_le_mul hL hp) (radix_power_le n)
  have hs4 : scale n ≤ (scale n)^4 := Nat.le_self_pow (by decide) _
  unfold LightGuardedWanted.keyBound
  nlinarith only [hm,hP,hs4]

noncomputable section

theorem localEnvelope_powerBound : PowerBound localEnvelope 0 := by
  refine ArithmeticStageBounds.powerBound_mono (g := localSearch 5000000) ?_ ?_
  · intro d hd
    simpa only [zero_add] using localSearch_subpolynomial 5000000 hd
  · filter_upwards [(microHalf_tendsto_atTop.comp inputBits_tendsto_atTop).eventually
      (eventually_ge_atTop 1)] with n hn
    exact LightLocalCoverInitResources.envelope_le_search hn

theorem scale_powerBound : PowerBound scale 2048 := by
  have hl := localEnvelope_powerBound.mono_exponent (by norm_num : (0 : ℝ) ≤ 2048)
  have hp := maxMod_powerBound.mono_exponent (show (Parameters.E+1/2)/5 ≤ (2048 : ℝ) by
    have hh := Parameters.E_bounds.2; linarith)
  have hy := window_powerBound.mono_exponent (by norm_num : (0 : ℝ) ≤ 2048)
  have hn := identity_powerBound.mono_exponent (by norm_num : (1 : ℝ) ≤ 2048)
  have hc := (PowerBound.const 100).mono_exponent (by norm_num : (0 : ℝ) ≤ 2048)
  exact ((((SharedReportingBankResourceBounds.magnitude_powerBound.add_same hl).add_same hp).add_same hy).add_same hn).add_same hc

end
end ThreeSum.EncodedColorResources

end

section


/-! # Polynomial bounds for the retained local cover and complete global key array -/

namespace ThreeSum.EncodedColorResources

open Scales BandScales ArithmeticStageBounds StageBounds GlobalEncoding LocalCoverBounds

set_option maxHeartbeats 2000000
set_option maxRecDepth 12000





















































theorem global_keys_word_bound (n : ℕ) : LightGlobalKeys.word (half n) (blocks n) ≤ 1000*(scale n)^5 := by
  have hb := (scale_bounds n).1
  have H := local_bounds n
  have hL := H.width
  have hP := H.prime
  have hS := H.rounds
  have hJ := (dimensions n).2.1
  have hpow : 2^(512*half n+1) ≤ scale n := by have hh := H.maskPower; omega
  have hprod := Nat.mul_le_mul hL (show localPrime (half n) ≤ scale n by omega)
  have hLP := Nat.mul_le_mul (show 512*half n ≤ scale n by omega) (show localPrime (half n) ≤ scale n by omega)
  have hkey := Nat.mul_le_mul (show localPrime (half n) ≤ scale n by omega)
    (Nat.mul_le_mul hLP (radix_power_le n))
  have hp5 : scale n ≤ (scale n)^5 := Nat.le_self_pow (by decide) _
  have hp25 := Nat.pow_le_pow_right (by omega : 1 ≤ scale n) (by decide : 2 ≤ 5)
  unfold LightGlobalKeys.word LightLocalKeys.word LightLocalKeyRow.word LightOneHot.word
    LightRadixKeys.word LightRadixRows.word
  nlinarith only [hb,hL,hP,hS,hJ,hpow,hprod,hLP,hkey,hp5,hp25]

theorem cover_word_bound (n : ℕ) : LightCoverKeys.word (half n) (blocks n) ≤ 1000*(scale n)^5 := by
  have hlocal := (LightLocalCoverInitResources.word_bound (half n)).trans (scale_bounds n).2.2.2.1
  have hp5 : scale n ≤ (scale n)^5 := Nat.le_self_pow (by decide) _
  unfold LightCoverKeys.word
  exact max_le (by omega) (global_keys_word_bound n)

end ThreeSum.EncodedColorResources

end

section


/-! # Affine storage and finite word bounds for the unchanged prime host -/

namespace ThreeSum.EncodedColorResources

open Scales BandScales ArithmeticStageBounds StageBounds GlobalEncoding LocalCoverBounds
open EncodedColorLayout KaratsubaInterface

set_option maxHeartbeats 2400000
set_option maxRecDepth 13000

theorem count_le (n : ℕ) : ColorBandBounds.count n (bandSize n) ≤ 3*(scale n)^2 := by
  have hn : n ≤ scale n := by have h := (scale_bounds n).2.1; omega
  exact (LightBandRawAResources.count_le n (bandSize n)).trans (Nat.mul_le_mul_left 3 (Nat.pow_le_pow_left hn 2))

theorem incidence_cap_le (n : ℕ) : EncodedColorStageCosts.incidenceCap n ≤ 3*(scale n)^3 := by
  have hh := Nat.mul_le_mul (dimensions n).2.2.2.1 (count_le n)
  unfold EncodedColorStageCosts.incidenceCap
  nlinarith only [hh]



















































































































































theorem prime_depth_bound (n : ℕ) : LightEncodedColorPrimeHost.depth n ≤ 10*scale n := by
  have hb := (scale_bounds n).1
  have hn := (scale_bounds n).2.1
  have hW := (Nat.add_le_add_right (LightScales.inputBits_le_self n) 1).trans hn
  have hp := (scale_bounds n).2.2.2.2.1
  have hraw := LightBandRawAResources.depth_le (inputBits n+1) n (bandSize n)
  have hc := (LightBandRawAResources.clog_le_self (maxMod n)).trans hp
  unfold LightEncodedColorPrimeHost.depth
  apply max_le <;> omega

end ThreeSum.EncodedColorResources

end

section


/-! # Finite affine resource bounds for balanced wanted records and shared sources -/

namespace ThreeSum.EncodedColorResources

open Scales BandScales ArithmeticStageBounds StageBounds GlobalEncoding LocalCoverBounds
open KaratsubaInterface

set_option maxHeartbeats 2400000
set_option maxRecDepth 13000
























































theorem wanted_word_bound (n U : ℕ) :
    LightGuardedWanted.word (maxMod n) (radix n) (half n) (blocks n) U
      (EncodedColorStageCosts.incidenceCap n) ≤ 150000*(scale n)^9+4*U := by
  have hb := (scale_bounds n).1
  have hlen := incidence_cap_le n
  have hG := totalKeys_le n
  have hM := (dimensions n).2.2.2.2
  have hP := (scale_bounds n).2.2.2.2.1
  have hbound := keyBound_le n
  have hcover := cover_word_bound n
  have hcapacity := (capacity_lt_twice (radix_pos n)).le.trans (Nat.mul_le_mul_left 2 hM)
  have hp3 : scale n ≤ (scale n)^3 := Nat.le_self_pow (by decide) _
  have hp23 := Nat.pow_le_pow_right (by omega : 1 ≤ scale n) (by decide : 2 ≤ 3)
  have hp9 : scale n ≤ (scale n)^9 := Nat.le_self_pow (by decide) _
  have hp49 := Nat.pow_le_pow_right (by omega : 1 ≤ scale n) (by decide : 4 ≤ 9)
  have hp59 := Nat.pow_le_pow_right (by omega : 1 ≤ scale n) (by decide : 5 ≤ 9)
  have hN : 3*EncodedColorStageCosts.incidenceCap n+LightGuardedWanted.totalKeys (half n) (blocks n)+1 ≤
      11*(scale n)^3 := by nlinarith only [hb,hlen,hG,hp3,hp23]
  have hkar : LightKaratsuba.wordBound (capacity (radix n))
      (3*EncodedColorStageCosts.incidenceCap n+LightGuardedWanted.totalKeys (half n) (blocks n)) ≤
      123904*(scale n)^9 := by
    unfold LightKaratsuba.wordBound
    calc
      _ ≤ 128*(2*scale n)^3*(11*(scale n)^3)^2 := by gcongr
      _ = _ := by ring
  have hbalanced : LightBalancedWanted.word (radix n) (3*EncodedColorStageCosts.incidenceCap n)
      (LightGuardedWanted.totalKeys (half n) (blocks n))
      (LightGuardedWanted.keyBound (maxMod n) (half n) (blocks n)) ≤ 150000*(scale n)^9 := by
    unfold LightBalancedWanted.word LightOriginalOffset.word LightSourceResidues.word
    apply max_le <;> nlinarith only [hb,hM,hbound,hkar,hp9,hp49]
  unfold LightGuardedWanted.word
  refine max_le ?_ (max_le ?_ ?_)
  · nlinarith only [hcover,hp59]
  · unfold LightRawAKeys.word
    nlinarith only [hb,hP,hp9]
  · omega













theorem stage_word_bound (n U : ℕ) :
    EncodedColorStageCosts.word n (maxMod n) (radix n) U (EncodedColorStageCosts.incidenceCap n) ≤
      150000*(scale n)^9+4*U := by
  have hw := wanted_word_bound n U
  have hs := source_word_bound n U
  have hp39 := Nat.pow_le_pow_right (by have h := (scale_bounds n).1; omega : 1 ≤ scale n) (by decide : 3 ≤ 9)
  unfold EncodedColorStageCosts.word LightEncodedColorWantedSources.word
  exact max_le hw (by omega)

















end ThreeSum.EncodedColorResources

end

section


/-! # Polynomial Need for the exact closed selected-color pipeline -/

namespace ThreeSum.EncodedColorResources

open Light Scales BandScales ArithmeticStageBounds StageBounds

set_option maxHeartbeats 2000000
set_option maxRecDepth 12000



















theorem pipeline_word_bound (n U : ℕ) :
    LightEncodedColorPipeline.word n U ≤ 200000*(scale n)^9+9*U := by
  have hb := (scale_bounds n).1
  have hprime := prime_word_bound n U
  have hstage := stage_word_bound n U
  have hcap := incidence_cap_le n
  have hP := (scale_bounds n).2.2.2.2.1
  have hM := (dimensions n).2.2.2.2
  have hg := (dimensions n).2.2.2.1
  have hh := (local_bounds n).width
  have hJ := (dimensions n).2.1
  have hcut := (dimensions n).2.2.1
  have hS := (powers n).2.1
  have hp9 : scale n ≤ (scale n)^9 := Nat.le_self_pow (by decide) _
  have hp39 := Nat.pow_le_pow_right (by omega : 1 ≤ scale n) (by decide : 3 ≤ 9)
  have hp69 := Nat.pow_le_pow_right (by omega : 1 ≤ scale n) (by decide : 6 ≤ 9)
  have hmax : max (LightEncodedColorPrimeHost.inputWord n U)
      (EncodedColorStageCosts.word n (maxMod n) (radix n) U (EncodedColorStageCosts.incidenceCap n)) ≤
      150000*(scale n)^9+9*U := max_le (by omega) (by omega)
  unfold LightEncodedColorPipeline.word
  change max (LightEncodedColorPrimeHost.inputWord n U)
    (EncodedColorStageCosts.word n (maxMod n) (radix n) U (EncodedColorStageCosts.incidenceCap n))+
    EncodedColorStageCosts.incidenceCap n+maxMod n+radix n+bandSize n+half n+blocks n+mu n+
    LightBlockSourceCatalog.count (half n) (blocks n)+100 ≤ _
  nlinarith only [hb,hmax,hcap,hP,hM,hg,hh,hJ,hcut,hS,hp9,hp39]

theorem pipeline_depth_bound (n : ℕ) : LightEncodedColorPipeline.depth n ≤ 30*(scale n)^3 := by
  have hb := (scale_bounds n).1
  have hp := prime_depth_bound n
  have hs := stage_depth_bound n
  have hp3 : scale n ≤ (scale n)^3 := Nat.le_self_pow (by decide) _
  unfold LightEncodedColorPipeline.depth
  omega






theorem need_bounds (n U : ℕ) :
    (need n U).word ≤ envelope n*(U+1) ∧
    (need n U).cells ≤ envelope n*(U+1) ∧
    (need n U).depth ≤ envelope n*(U+1) := by
  have hb := (scale_bounds n).1
  have hp10 : 1 ≤ (scale n)^10 := Nat.one_le_pow _ _ (by omega)
  have hmul : (scale n)^10 ≤ (scale n)^10*(U+1) := Nat.le_mul_of_pos_right _ (by omega)
  have hU : U ≤ (scale n)^10*(U+1) := (Nat.le_succ _).trans (Nat.le_mul_of_pos_left _ hp10)
  have hp39 := Nat.pow_le_pow_right (by omega : 1 ≤ scale n) (by decide : 3 ≤ 10)
  have hp59 := Nat.pow_le_pow_right (by omega : 1 ≤ scale n) (by decide : 5 ≤ 10)
  have hp99 := Nat.pow_le_pow_right (by omega : 1 ≤ scale n) (by decide : 9 ≤ 10)
  have hw := pipeline_word_bound n U
  have hd := pipeline_depth_bound n
  rw [show envelope n*(U+1)=1000000*((scale n)^10*(U+1)) by unfold envelope; ring]
  change LightEncodedColorPipeline.word n U ≤ _ ∧ 3000*(scale n)^5+U ≤ _ ∧
    LightEncodedColorPipeline.depth n ≤ _
  constructor
  · omega
  · constructor <;> omega

noncomputable section

theorem envelope_powerBound : PowerBound envelope 20480 := by
  have hh := (PowerBound.const 1000000).mul (scale_powerBound.pow 10)
  convert hh using 1 <;> (first | rfl | norm_num)

theorem poly_need : Light.PolyNeed need := by
  apply PolynomialResources.polyNeed_of_envelope envelope_powerBound 1
  · intro n U; simpa only [pow_one] using (need_bounds n U).1
  · intro n U; simpa only [pow_one] using (need_bounds n U).2.1
  · intro n U; simpa only [pow_one] using (need_bounds n U).2.2

end
























end ThreeSum.EncodedColorResources

end

section


/-! # Affine resources for source construction followed by reporting setup -/

namespace ThreeSum.EncodedColorReportingResources

open Light Scales BandScales ThreeSumReportingSetupData

set_option maxHeartbeats 1800000
set_option maxRecDepth 12000































noncomputable section

theorem poly_need_sourceProof : Light.PolyNeed need := by
  obtain ⟨sa,ka,ha⟩ := EncodedColorResources.poly_need
  obtain ⟨sb,kb,hb⟩ := ThreeSumReportingSetupResources.poly_need
  refine ⟨sa+sb+3,ka+kb,fun n U => ?_⟩
  let F := Light.polyBound (sa+sb) (ka+kb) [n,U]
  have hA := ha n U
  have hB := hb n U
  have hma : Light.polyBound sa ka [n,U] ≤ F := Light.polyBound_mono (by omega) (by omega) _
  have hmb : Light.polyBound sb kb [n,U] ≤ F := Light.polyBound_mono (by omega) (by omega) _
  have hF : 1 ≤ F := by
    unfold F Light.polyBound
    simp only [List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one]
    exact Nat.mul_pos (by positivity) (by positivity)
  have he : Light.polyBound (sa+sb+3) (ka+kb) [n,U]=8*F := by
    unfold F Light.polyBound
    rw [pow_add]
    norm_num
    ring
  rw [he]
  dsimp only [need]
  exact ⟨by omega,by omega,by omega⟩

end
end ThreeSum.EncodedColorReportingResources

end


theorem solution : Light.PolyNeed ThreeSum.EncodedColorReportingResources.need := by
  exact @ThreeSum.EncodedColorReportingResources.poly_need_sourceProof

#print axioms solution
