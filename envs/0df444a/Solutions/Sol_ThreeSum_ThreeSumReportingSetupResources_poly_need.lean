-- Prove2me | solution 1 for ThreeSum.ThreeSumReportingSetupResources.poly_need
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-10-14T16:29:15.072283+00:00
-- url     : https://prove2.me/submissions/e867fb38-db20-4518-9af8-b1a9712d1c3c

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
import Definitions.Def_ThreeSum1962Source_Bundle07
import Definitions.Def_ThreeSum1962Source_Bundle08
import Definitions.Def_ThreeSum1962Source_Bundle09
import Definitions.Def_ThreeSum1962Source_Bundle10
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
import Theorems.Thm_ThreeSum_KaratsubaInterface_capacity_lt_twice
import Theorems.Thm_ThreeSum_PolynomialResources_pair_polyBound_of_powerBound
import Theorems.Thm_ThreeSum_Scales_natSqrt_ratio_tendsto_zero
import Theorems.Thm_ThreeSum_SharedReportingBankResourceBounds_components
import Theorems.Thm_ThreeSum_SharedReportingBankResourceBounds_dense_word_le
import Theorems.Thm_ThreeSum_SharedReportingBankResourceBounds_scaled_extent_le
import Theorems.Thm_ThreeSum_SharedReportingBankResourceBounds_scaled_word_le
import Theorems.Thm_ThreeSum_StageBounds_PowerBound_add_same


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
namespace ThreeSum.SharedReportingBankHeader
end ThreeSum.SharedReportingBankHeader
namespace ThreeSum.SharedReportingBankLayout
end ThreeSum.SharedReportingBankLayout
namespace ThreeSum.StageBounds
end ThreeSum.StageBounds
namespace ThreeSum.SubsetAddress
end ThreeSum.SubsetAddress
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



















theorem maxMod_pos (n : ℕ) : 0 < maxMod n := by
  unfold maxMod
  exact Nat.mul_pos (radix_pos n) (Nat.pow_pos (by have := primeWindow_ge_two n; omega))






























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


/-! # Finite scale bounds for every shared-bank resource component -/

namespace ThreeSum.SharedReportingBankResourceBounds

open Scales Light SubsetAddress SharedReportingBankLayout SharedReportingBankHeader

set_option maxHeartbeats 3000000
set_option maxRecDepth 14000































































































































































































theorem scaled_depth_le (n : ℕ) : scaledDepth n ≤ polynomialPart n := by
  have H := components n
  have hM := H.positive
  have hL := H.localWidthBound
  have hW := H.widthBound
  have hK := H.levelsBound
  have hp : magnitude n+1 ≤ (magnitude n+1)^5 := Nat.le_self_pow (by decide) _
  have hn : 1 ≤ (n+1)^2 := Nat.one_le_pow _ _ (by omega)
  have hm := Nat.le_mul_of_pos_right (5000*(magnitude n+1)^5) hn
  unfold scaledDepth depth polynomialPart
  nlinarith














































































end ThreeSum.SharedReportingBankResourceBounds

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

theorem polynomial_part_powerBound : PowerBound polynomialPart 10242 := by
  have hm := magnitude_powerBound.add_same
    ((PowerBound.const 1).mono_exponent (by norm_num : (0 : ℝ) ≤ 2048))
  have hn := ArithmeticStageBounds.identity_powerBound.add_same
    ((PowerBound.const 1).mono_exponent (by norm_num : (0 : ℝ) ≤ 1))
  have hh := ((PowerBound.const 5000).mul (hm.pow 5)).mul (hn.pow 2)
  convert hh using 1 <;> (first | rfl | norm_num [polynomialPart])

theorem envelope_powerBound : PowerBound envelope 131072 := by
  have hp := polynomial_part_powerBound.mono_exponent
    (by norm_num : (10242 : ℝ) ≤ 131072)
  have hm : PowerBound (fun n => (magnitude n)^64) 131072 := by
    convert magnitude_powerBound.pow 64 using 1 <;> norm_num
  exact hp.add_same hm

theorem scaled_extent_le_envelope (n : ℕ) : scaledExtent n ≤ envelope n :=
  (scaled_extent_le n).trans (Nat.le_add_right _ _)

theorem scaled_depth_le_envelope (n : ℕ) : scaledDepth n ≤ envelope n :=
  (scaled_depth_le n).trans (Nat.le_add_right _ _)












theorem poly_need : Light.PolyNeed need := by
  apply PolynomialResources.polyNeed_of_envelope envelope_powerBound 0
  · intro n U; simpa only [need,pow_zero,mul_one] using scaled_word_le n
  · intro n U; simpa only [need,pow_zero,mul_one] using scaled_extent_le_envelope n
  · intro n U; simpa only [need,pow_zero,mul_one] using scaled_depth_le_envelope n







end
end ThreeSum.SharedReportingBankResourceBounds

end

section


/-! # Resource bounds for the complete h-and-free local-cover initializer -/

namespace ThreeSum.LightLocalCoverInitResources

open Light LocalCoverBounds GlobalEncoding LightLocalCoverSchedule LightLocalCoverTables
open LightLocalCoverLayout

set_option maxHeartbeats 1500000




























































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


/-! # Affine storage and finite word bounds for the unchanged prime host -/

namespace ThreeSum.EncodedColorResources

open Scales BandScales ArithmeticStageBounds StageBounds GlobalEncoding LocalCoverBounds
open EncodedColorLayout KaratsubaInterface

set_option maxHeartbeats 2400000
set_option maxRecDepth 13000





























































theorem capacity_bound (n : ℕ) : capacity (maxMod n) ≤ 2*scale n :=
  (capacity_lt_twice (maxMod_pos n)).le.trans (Nat.mul_le_mul_left 2 (scale_bounds n).2.2.2.2.1)







































































































end ThreeSum.EncodedColorResources

end

section


/-! # Exact finite resources for constructing the dense-stop counter

The power-loop bound includes its actual `(base+1)^(J+1)` intermediate.
The modular scoring workspace remains affine in an arbitrary destination.
-/

namespace ThreeSum.SharedReportingBankResourceBounds

open Light Scales BandScales ArithmeticStageBounds GlobalEncoding LocalCoverBounds
open KaratsubaInterface

set_option maxHeartbeats 2300000
set_option maxRecDepth 14000












































































































































theorem dense_cells_le (n U : ℕ) : denseCells n U ≤ 40*EncodedColorResources.scale n+U+20 := by
  have hp := (EncodedColorResources.scale_bounds n).2.2.2.2.1
  have hg := (EncodedColorResources.dimensions n).2.2.2.1
  have hc := EncodedColorResources.capacity_bound n
  have hlogp := Nat.log_le_self 2 (maxMod n+1)
  have hlogU := Nat.log_le_self 2 (U+1)
  unfold denseCells LightWeightedScore.space LightModuloCounts.space
  omega

theorem dense_depth_le (n : ℕ) : denseDepth n ≤ EncodedColorResources.scale n+8 := by
  have hh := (LightBandRawAResources.clog_le_self (maxMod n)).trans
    (EncodedColorResources.scale_bounds n).2.2.2.2.1
  unfold denseDepth
  omega

end ThreeSum.SharedReportingBankResourceBounds

end

section


/-! # Polynomial limits for the exact dense initialization resources -/

namespace ThreeSum.SharedReportingBankResourceBounds

open Light Scales StageBounds ArithmeticStageBounds

set_option maxHeartbeats 1600000
set_option maxRecDepth 14000






theorem dense_envelope_factors (n U : ℕ) :
    1 ≤ (EncodedColorResources.scale n)^8 ∧
    EncodedColorResources.scale n ≤ (EncodedColorResources.scale n)^8 ∧
    (EncodedColorResources.scale n)^8 ≤ (EncodedColorResources.scale n)^8*(U+1) ∧
    U ≤ (EncodedColorResources.scale n)^8*(U+1) := by
  have hS : 1 ≤ EncodedColorResources.scale n := by
    have hh := (EncodedColorResources.scale_bounds n).1
    omega
  have h1 : 1 ≤ (EncodedColorResources.scale n)^8 := Nat.one_le_pow _ _ hS
  exact ⟨h1,Nat.le_self_pow (by decide) _,Nat.le_mul_of_pos_right _ (by omega),
    (Nat.le_succ _).trans (Nat.le_mul_of_pos_left _ h1)⟩

theorem dense_word_bound (n U : ℕ) : denseWord n U ≤ denseEnvelope n*(U+1) := by
  obtain ⟨h1,_,hb,hU⟩ := dense_envelope_factors n U
  have hh := dense_word_le n U
  rw [show denseEnvelope n*(U+1)=20000*((EncodedColorResources.scale n)^8*(U+1)) by
    unfold denseEnvelope; ring]
  omega

theorem dense_cells_bound (n U : ℕ) : denseCells n U ≤ denseEnvelope n*(U+1) := by
  obtain ⟨h1,hS,hb,hU⟩ := dense_envelope_factors n U
  have hh := dense_cells_le n U
  rw [show denseEnvelope n*(U+1)=20000*((EncodedColorResources.scale n)^8*(U+1)) by
    unfold denseEnvelope; ring]
  omega

theorem dense_depth_bound (n : ℕ) : denseDepth n ≤ denseEnvelope n := by
  obtain ⟨h1,hS,_,_⟩ := dense_envelope_factors n 0
  have hh := dense_depth_le n
  unfold denseEnvelope
  omega

noncomputable section

theorem dense_envelope_powerBound : PowerBound denseEnvelope 16384 := by
  have hh := (PowerBound.const 20000).mul (EncodedColorResources.scale_powerBound.pow 8)
  convert hh using 1 <;> (first | rfl | norm_num [denseEnvelope])

theorem dense_poly_need : Light.PolyNeed denseNeed := by
  apply PolynomialResources.polyNeed_of_envelope dense_envelope_powerBound 1
  · intro n U; simpa only [denseNeed,pow_one] using dense_word_bound n U
  · intro n U; simpa only [denseNeed,pow_one] using dense_cells_bound n U
  · intro n U
    simpa only [denseNeed,pow_one] using
      (dense_depth_bound n).trans (Nat.le_mul_of_pos_right _ (by omega : 0<U+1))

end

















end ThreeSum.SharedReportingBankResourceBounds

end

section


/-! # Compose the two actual reporting allocations at an arbitrary free pointer -/

namespace ThreeSum.ThreeSumReportingSetupResources

open Light Scales BandScales ThreeSumReportingSetupData

set_option maxHeartbeats 1400000
set_option maxRecDepth 10000




























noncomputable section

theorem poly_need_sourceProof : Light.PolyNeed need := by
  obtain ⟨sa,ka,ha⟩ := SharedReportingBankResourceBounds.poly_need
  obtain ⟨sb,kb,hb⟩ := SharedReportingBankResourceBounds.dense_poly_need
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
  simp only [need]
  exact ⟨by omega,by omega,by omega⟩

end
end ThreeSum.ThreeSumReportingSetupResources

end


theorem solution : Light.PolyNeed ThreeSum.ThreeSumReportingSetupResources.need := by
  exact @ThreeSum.ThreeSumReportingSetupResources.poly_need_sourceProof

#print axioms solution
