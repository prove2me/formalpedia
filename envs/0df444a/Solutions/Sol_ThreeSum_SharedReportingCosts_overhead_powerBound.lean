-- Prove2me | solution 1 for ThreeSum.SharedReportingCosts.overhead_powerBound
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-10-14T15:05:51.068977+00:00
-- url     : https://prove2.me/submissions/61f40734-420d-4890-8618-9b5eb3a2239e

import Aesop
import Definitions.Def_APSPSource_RemainingDefinitions
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Logic
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Regions
import Definitions.Def_ThreeSum1962Source_Bundle01
import Definitions.Def_ThreeSum1962Source_Bundle07
import Definitions.Def_ThreeSum1962Source_Bundle10
import Definitions.Def_ThreeSum1962Source_Bundle15
import Definitions.Def_TrulySubcubicAPSP_SourceSpecification
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Group.Equiv.Basic
import Mathlib.Algebra.Group.Int.Defs
import Mathlib.Algebra.GroupWithZero.Nat
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Algebra.Order.BigOperators.Group.Multiset
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Floor.Div
import Mathlib.Algebra.Order.Group.Abs
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Algebra.Order.Group.Nat
import Mathlib.Algebra.Order.Group.Unbundled.Abs
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Algebra.Ring.Nat
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.NthRootLemmas
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Combinatorics.Colex
import Mathlib.Data.Bool.Basic
import Mathlib.Data.Fin.Embedding
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
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
import Mathlib.Data.Int.Cast.Lemmas
import Mathlib.Data.Int.ModEq
import Mathlib.Data.Int.Notation
import Mathlib.Data.Int.SuccPred
import Mathlib.Data.List.Basic
import Mathlib.Data.List.GetD
import Mathlib.Data.List.MinMax
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.OfFn
import Mathlib.Data.List.Pi
import Mathlib.Data.List.Sublists
import Mathlib.Data.List.TakeDrop
import Mathlib.Data.Nat.Cast.Order.Ring
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Count
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Data.Nat.Sqrt
import Mathlib.Data.Nat.SuccPred
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.Index
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.LinearAlgebra.Matrix.Dual
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Logic.Function.Basic
import Mathlib.NumberTheory.Bertrand
import Mathlib.NumberTheory.Chebyshev
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Order.Monotone.Basic
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Tactic.Abel
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.Tauto
import Theorems.Thm_ThreeSum_Scales_natSqrt_ratio_tendsto_zero
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
namespace ThreeSum.HierarchyScales
end ThreeSum.HierarchyScales
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
namespace ThreeSum.TrimScales
end ThreeSum.TrimScales
namespace ThreeSum.UniformStageBounds
end ThreeSum.UniformStageBounds

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























theorem bits_le_window_square (n : ℕ) : inputBits n+1 ≤ primeWindow n^2 := by
  have hroot := Nat.lt_succ_sqrt' (inputBits n)
  have hpow : Nat.sqrt (inputBits n)+1 ≤ 2^(Nat.sqrt (inputBits n)+1) :=
    (Nat.lt_pow_self (by decide : 1 < 2)).le
  have hs := Nat.pow_le_pow_left hpow 2
  unfold primeWindow windowExponent
  simp only [Nat.succ_eq_add_one] at hroot
  omega





















noncomputable section

theorem powerBound_mono {f g : ℕ → ℕ} {a : ℝ} (hg : PowerBound g a)
    (hfg : ∀ᶠ n : ℕ in atTop, f n ≤ g n) : PowerBound f a := by
  intro d hd
  filter_upwards [hg d hd, hfg] with n hn hm
  exact (show (f n : ℝ) ≤ (g n : ℝ) by exact_mod_cast hm).trans hn



























theorem window_powerBound : PowerBound primeWindow 0 :=
  PowerBound.of_rate primeWindow_log_ratio_tendsto_zero































































































end
end ThreeSum.ArithmeticStageBounds

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




theorem root_le_self (m : ℕ) : Nat.nthRoot 3 m ≤ m :=
  (Nat.le_self_pow (by decide : 3 ≠ 0) (Nat.nthRoot 3 m)).trans
    (Nat.pow_nthRoot_le (Or.inl (by decide : 3 ≠ 0)))




theorem microHalf_le_self (m : ℕ) : microHalf m ≤ m :=
  (Nat.div_le_self (Nat.nthRoot 3 m) 2).trans (root_le_self m)

theorem blockCount_le (m : ℕ) : blockCount m ≤ 20*m :=
  Nat.mul_le_mul_left 20 (Nat.div_le_self m (100*microSize m))


































































































































































end ThreeSum.LightScales

end

section


/-!
# Exponent of the complete shared-catalog invocation budget

The local balanced-pair enumeration and all polynomial factors in the
concrete52-procedure constructor have exponent zero. Multiplying the
existing box ledger by this overhead therefore preserves its exponent.
This charges catalog invocations; the surrounding bank iterator is separate.
-/

namespace ThreeSum.SharedReportingCosts

open Filter Real Scales Parameters StageBounds ArithmeticStageBounds
open scoped Topology

set_option maxHeartbeats 1500000

noncomputable section

theorem bits_powerBound : PowerBound inputBits 0 := by
  have hh : PowerBound (fun n => primeWindow n^2) 0 := by
    simpa only [mul_zero] using window_powerBound.pow 2
  exact powerBound_mono hh (Eventually.of_forall fun n => by
    have h := bits_le_window_square n
    omega)

theorem half_powerBound : PowerBound half 0 :=
  powerBound_mono bits_powerBound (Eventually.of_forall fun n =>
    LightScales.microHalf_le_self (inputBits n))

theorem blocks_powerBound : PowerBound blocks 0 := by
  have hh : PowerBound (fun n => 20*inputBits n) 0 := by
    simpa only [zero_add] using (PowerBound.const 20).mul bits_powerBound
  exact powerBound_mono hh (Eventually.of_forall fun n =>
    LightScales.blockCount_le (inputBits n))

theorem local_width_powerBound : PowerBound localWidth 0 := by
  change PowerBound (fun n => 512*half n) 0
  simpa only [zero_add] using (PowerBound.const 512).mul half_powerBound

theorem width_powerBound : PowerBound width 0 := by
  change PowerBound (fun n => blocks n*localWidth n) 0
  simpa only [zero_add] using blocks_powerBound.mul local_width_powerBound

theorem overhead_powerBound_sourceProof : PowerBound overhead 0 := by
  have hw := width_powerBound.add_same (PowerBound.const 1)
  have hl := local_width_powerBound.add_same (PowerBound.const 1)
  have hj := blocks_powerBound.add_same (PowerBound.const 1)
  have hs : PowerBound (localSearch 257) 0 :=
    PowerBound.of_rate (localSearch_log_ratio_tendsto_zero 257)
  have ht1 : PowerBound (fun n => 100000*(width n+1)^5) 0 := by
    simpa only [mul_zero, zero_add] using (PowerBound.const 100000).mul (hw.pow 5)
  have ht2 : PowerBound (fun n => 5000*(localWidth n+1)^2*(localSearch 257 n+1)) 0 := by
    simpa only [mul_zero, zero_add] using
      ((PowerBound.const 5000).mul (hl.pow 2)).mul (hs.add_same (PowerBound.const 1))
  have ht3 : PowerBound (fun n => 1200*(blocks n+1)) 0 := by
    simpa only [zero_add] using (PowerBound.const 1200).mul hj
  have ht4 : PowerBound (fun n => 2000*(width n+1)) 0 := by
    simpa only [zero_add] using (PowerBound.const 2000).mul hw
  exact (((ht1.add_same ht2).add_same ht3).add_same ht4).add_same (PowerBound.const 1050)





















end
end ThreeSum.SharedReportingCosts

end


theorem solution : ThreeSum.StageBounds.PowerBound ThreeSum.SharedReportingCosts.overhead
  (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) := by
  exact @ThreeSum.SharedReportingCosts.overhead_powerBound_sourceProof

#print axioms solution
