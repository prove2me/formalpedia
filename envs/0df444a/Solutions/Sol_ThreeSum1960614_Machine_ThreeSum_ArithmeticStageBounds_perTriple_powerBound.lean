-- Prove2me | solution 1 for ThreeSum1960614.Machine.ThreeSum.ArithmeticStageBounds.perTriple_powerBound
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-15T09:21:26.42027+00:00
-- url     : https://prove2.me/submissions/e6717e29-3b49-4f7b-a1f1-f910ee18fdd9

import Aesop
import Definitions.Def_APSPSource_RemainingDefinitions
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Regions
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Syntax
import Definitions.Def_APSPSource_ThreeSumApsp_Util_Index
import Definitions.Def_APSPSource_ThreeSumApsp_Util_List
import Definitions.Def_ThreeSum1960614_Analysis
import Definitions.Def_ThreeSum1960614_Machine_Bundle001
import Definitions.Def_ThreeSum1960614_Machine_Bundle003
import Definitions.Def_ThreeSum1960614_Machine_Bundle004
import Definitions.Def_ThreeSum1960614_Machine_Bundle005
import Definitions.Def_ThreeSum1960614_Machine_Bundle006
import Definitions.Def_ThreeSum1960614_Machine_Bundle007
import Definitions.Def_ThreeSum1960614_Machine_Bundle008
import Definitions.Def_ThreeSum1960614_Machine_Bundle009
import Definitions.Def_ThreeSum1960614_Machine_Bundle010
import Definitions.Def_ThreeSum1960614_Machine_Bundle011
import Definitions.Def_ThreeSum1960614_Machine_Bundle012
import Definitions.Def_ThreeSum1960614_Machine_Bundle013
import Definitions.Def_ThreeSum1960614_Machine_Bundle014
import Definitions.Def_ThreeSum1960614_Machine_Bundle016
import Definitions.Def_ThreeSum1960614_Machine_Bundle018
import Definitions.Def_ThreeSum1960614_Machine_Bundle020
import Definitions.Def_ThreeSum1960614_Machine_Bundle021
import Definitions.Def_ThreeSum1962Source_Bundle01
import Definitions.Def_ThreeSum1962Source_Bundle02
import Definitions.Def_ThreeSum1962Source_Bundle03
import Definitions.Def_ThreeSum1962Source_Bundle04
import Definitions.Def_ThreeSum1962Source_Bundle05
import Definitions.Def_ThreeSum1962Source_Bundle06
import Definitions.Def_ThreeSum1962Source_Bundle07
import Definitions.Def_ThreeSum1962Source_Bundle09
import Definitions.Def_TrulySubcubicAPSP_SourceSpecification
import Lean
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Group.Equiv.Basic
import Mathlib.Algebra.Group.Int.Defs
import Mathlib.Algebra.GroupWithZero.Nat
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Algebra.Order.BigOperators.Group.Multiset
import Mathlib.Algebra.Order.Chebyshev
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
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
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
import Mathlib.Data.Finset.Range
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Int.ModEq
import Mathlib.Data.Int.Notation
import Mathlib.Data.List.GetD
import Mathlib.Data.List.MinMax
import Mathlib.Data.List.Pi
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
import Mathlib.Logic.Function.Basic
import Mathlib.NumberTheory.Bertrand
import Mathlib.NumberTheory.Chebyshev
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Order.Monotone.Basic
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Tactic
import Mathlib.Tactic.Abel
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
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Data.Int.Cast.Lemmas
import Mathlib.Data.Nat.Cast.Order.Ring
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Theorems.Thm_ThreeSum_ArithmeticStageBounds_powerBound_of_fifth
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_BandScales_bandSize_log_rate
import Theorems.Thm_ThreeSum_StageBounds_PowerBound_add_same
import Theorems.Thm_ThreeSum_ModuloCosts_roundedPower_fifth
import Theorems.Thm_ThreeSum_Scales_natSqrt_ratio_tendsto_zero

private theorem ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound.add_same {f g : ℕ → ℕ} {a : ℝ}
    (hf : _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound f a)
    (hg : _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound g a) :
    _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound (fun n => f n+g n) a := by
  exact _root_.ThreeSum.StageBounds.PowerBound.add_same hf hg


local instance platformRadixNonzero_50b3de8930 (n : ℕ) : NeZero (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.radix n) :=
  ⟨Nat.ne_of_gt (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.radix_pos n)⟩


namespace Filter
end Filter
namespace Real
end Real
namespace ThreeSum
end ThreeSum
namespace ThreeSum.ArithmeticStageBounds
end ThreeSum.ArithmeticStageBounds
namespace ThreeSum.CostLedger
end ThreeSum.CostLedger
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
namespace ThreeSum.StageBounds.PowerBound
end ThreeSum.StageBounds.PowerBound
namespace ThreeSum1960614.Machine.ThreeSum
end ThreeSum1960614.Machine.ThreeSum
namespace ThreeSum1960614.Machine.ThreeSum.ArithmeticStageBounds
end ThreeSum1960614.Machine.ThreeSum.ArithmeticStageBounds
namespace ThreeSum1960614.Machine.ThreeSum.BandScales
end ThreeSum1960614.Machine.ThreeSum.BandScales
namespace ThreeSum1960614.Machine.ThreeSum.CostLedger
end ThreeSum1960614.Machine.ThreeSum.CostLedger
namespace ThreeSum1960614.Machine.ThreeSum.HierarchyScales
end ThreeSum1960614.Machine.ThreeSum.HierarchyScales
namespace ThreeSum1960614.Machine.ThreeSum.MassScales
end ThreeSum1960614.Machine.ThreeSum.MassScales
namespace ThreeSum1960614.Machine.ThreeSum.ModuloCosts
end ThreeSum1960614.Machine.ThreeSum.ModuloCosts
namespace ThreeSum1960614.Machine.ThreeSum.Parameters
end ThreeSum1960614.Machine.ThreeSum.Parameters
namespace ThreeSum1960614.Machine.ThreeSum.Scales
end ThreeSum1960614.Machine.ThreeSum.Scales
namespace ThreeSum1960614.Machine.ThreeSum.StageBounds
end ThreeSum1960614.Machine.ThreeSum.StageBounds
namespace ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound
end ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound
namespace ThreeSum1960614.Machine.ThreeSum.Switch
end ThreeSum1960614.Machine.ThreeSum.Switch
namespace ThreeSum1960614.Machine.ThreeSum.TrimScales
end ThreeSum1960614.Machine.ThreeSum.TrimScales
namespace ThreeSum1960614.Machine.ThreeSum.UniformStageBounds
end ThreeSum1960614.Machine.ThreeSum.UniformStageBounds

namespace ThreeSum1960614.Machine

/-!
# The actual integer block schedule

All four size parameters below are executable natural-number functions.
The finite bounds and limits concern these functions, including the even
rounding of the cube root and the divisibility constraints on the number
of blocks.  No asymptotic size premise is imposed on the schedule.
-/

namespace ThreeSum.Scales
open _root_.ThreeSum.Scales


open _root_.Filter
open _root_.Real
open scoped _root_.Topology





















































noncomputable section







































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
    Tendsto (fun m : ℕ => (_root_.ThreeSum.Scales.windowExponent m : ℝ) / m) atTop (𝓝 0) := by
  have h := _root_.ThreeSum.Scales.natSqrt_ratio_tendsto_zero.add
    (tendsto_natCast_atTop_atTop (R := ℝ)).inv_tendsto_atTop
  simpa [_root_.ThreeSum.Scales.windowExponent, Nat.cast_add, add_div, one_div] using h





theorem primeWindow_log_ratio_tendsto_zero :
    Tendsto (fun n : ℕ => Real.log (_root_.ThreeSum.Scales.primeWindow n : ℝ) / Real.log n) atTop (𝓝 0) := by
  have h := ((_root_.ThreeSum1960614.Machine.ThreeSum.Scales.windowExponent_ratio_tendsto_zero.comp _root_.ThreeSum.Scales.inputBits_tendsto_atTop).mul
    _root_.ThreeSum.Scales.inputBits_log_ratio_tendsto).const_mul (Real.log 2)
  simp only [zero_mul, mul_zero] at h
  apply h.congr'
  filter_upwards [_root_.ThreeSum.Scales.inputBits_tendsto_atTop.eventually (eventually_ge_atTop 1)] with n hn
  have hn0 : (_root_.ThreeSum.Scales.inputBits n : ℝ) ≠ 0 := by exact_mod_cast (by omega : inputBits n ≠ 0)
  simp only [Function.comp_def, _root_.ThreeSum.Scales.primeWindow, Nat.cast_pow, Real.log_pow, Nat.cast_ofNat]
  field_simp













































































end

end ThreeSum.Scales

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

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
open _root_.ThreeSum.MassScales


open _root_.Filter
open _root_.Real
open _root_.ThreeSum.Parameters
open _root_.ThreeSum1960614.Machine.ThreeSum.Parameters
open _root_.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.TrimScales
open _root_.ThreeSum1960614.Machine.ThreeSum.BandScales
open _root_.ThreeSum.CostLedger
open _root_.ThreeSum1960614.Machine.ThreeSum.CostLedger
open _root_.ThreeSum1960614.Machine.ThreeSum.HierarchyScales
open scoped _root_.Topology

set_option maxHeartbeats 1000000
set_option maxRecDepth 10000























noncomputable section





theorem nat_log_rate_const (c : ℕ) :
    Tendsto (fun n : ℕ => Real.log (c : ℝ) / Real.log n) atTop (𝓝 0) := by
  simpa only [mul_zero, Pi.inv_apply, div_eq_mul_inv] using
    _root_.ThreeSum.Asymptotics.log_nat_tendsto_atTop.inv_tendsto_atTop.const_mul (Real.log (c : ℝ))









theorem bandSize_log_rate_shift :
    Tendsto (fun n : ℕ => Real.log (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n : ℝ) / Real.log n) atTop
      (𝓝 (_root_.ThreeSum1960614.Machine.ThreeSum.Parameters.epsilon * (_root_.ThreeSum1960614.Machine.ThreeSum.Parameters.E + _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.bandShift))) := by
  simpa only [_root_.ThreeSum1960614.Machine.ThreeSum.Parameters.bandShift, sub_eq_add_neg] using _root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize_log_rate



















end
end ThreeSum.MassScales

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# The six principal finite stage counts

This module assembles actual natural-number work quantities.  Its final
theorem is a runtime-ledger target, not a 3SUM correctness or machine-time
theorem.  The only input-dependent assumptions are four explicit finite
counting inequalities for the wanted mass and the prime-chain score.
An implementation must still connect its operation counter to these counts.
-/

namespace ThreeSum.StageBounds
open _root_.ThreeSum.StageBounds


open _root_.Filter
open _root_.Real
open _root_.ThreeSum.Parameters
open _root_.ThreeSum1960614.Machine.ThreeSum.Parameters
open _root_.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.TrimScales
open _root_.ThreeSum1960614.Machine.ThreeSum.BandScales
open _root_.ThreeSum1960614.Machine.ThreeSum.Switch
open _root_.ThreeSum.CostLedger
open _root_.ThreeSum1960614.Machine.ThreeSum.CostLedger
open _root_.ThreeSum1960614.Machine.ThreeSum.HierarchyScales
open _root_.ThreeSum.MassScales
open _root_.ThreeSum1960614.Machine.ThreeSum.MassScales
open scoped _root_.Topology

set_option maxHeartbeats 1000000
set_option maxRecDepth 10000





















noncomputable section



namespace PowerBound
open _root_.ThreeSum.StageBounds.PowerBound


theorem of_rate {f : ℕ → ℕ} {a : ℝ}
    (hf : Tendsto (fun n : ℕ => Real.log (f n : ℝ) / Real.log n) atTop (𝓝 a)) : _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound f a :=
  fun _ hd => _root_.ThreeSum1960614.Machine.ThreeSum.Scales.eventually_le_rpow_of_log_ratio hf hd

theorem const (c : ℕ) : _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound (fun _ => c) 0 := _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound.of_rate (_root_.ThreeSum1960614.Machine.ThreeSum.MassScales.nat_log_rate_const c)

theorem mul {f g : ℕ → ℕ} {a b : ℝ} (hf : _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound f a) (hg : _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound g b) :
    _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound (fun n => f n * g n) (a + b) := by
  intro d hd
  filter_upwards [hf (d / 2) (by linarith), hg (d / 2) (by linarith),
    eventually_ge_atTop (1 : ℕ)] with n hfn hgn hn
  have hnR : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  rw [Nat.cast_mul]
  calc
    _ ≤ (n : ℝ) ^ (a + d / 2) * (n : ℝ) ^ (b + d / 2) :=
      mul_le_mul hfn hgn (Nat.cast_nonneg _) (Real.rpow_nonneg hnR.le _)
    _ = (n : ℝ) ^ ((a + b) + d) := by rw [← Real.rpow_add hnR]; congr 1; ring

theorem mono_exponent {f : ℕ → ℕ} {a b : ℝ} (hf : _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound f a) (hab : a ≤ b) :
    _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound f b := by
  intro d hd
  filter_upwards [hf d hd, eventually_ge_atTop (1 : ℕ)] with n hn hge
  exact hn.trans (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hge) (by linarith))



theorem pow {f : ℕ → ℕ} {a : ℝ} (hf : _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound f a) (k : ℕ) :
    _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound (fun n => f n ^ k) ((k : ℝ) * a) := by
  induction k with
  | zero => simpa only [Nat.cast_zero, zero_mul, pow_zero] using _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound.const 1
  | succ k ih =>
      simpa only [Nat.pow_succ, Nat.cast_add, Nat.cast_one, add_mul, one_mul] using ih.mul hf

end PowerBound

































end
end ThreeSum.StageBounds

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# The arithmetic and balancing work outside the six reporting stages

The finite bounds here include complete modular-counting invocations, their
signed-remainder bit cost, and the actual correlation/minimum routine. They
augment the six-stage reporting budget. The whole solver still has to charge
its actual host operations to this combined budget.
-/

namespace ThreeSum.ArithmeticStageBounds
open _root_.ThreeSum.ArithmeticStageBounds


open _root_.Filter
open _root_.Real
open _root_.ThreeSum.Parameters
open _root_.ThreeSum1960614.Machine.ThreeSum.Parameters
open _root_.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.BandScales
open _root_.ThreeSum.CostLedger
open _root_.ThreeSum1960614.Machine.ThreeSum.CostLedger
open _root_.ThreeSum1960614.Machine.ThreeSum.HierarchyScales
open _root_.ThreeSum.MassScales
open _root_.ThreeSum1960614.Machine.ThreeSum.MassScales
open _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.UniformStageBounds
open _root_.ThreeSum.ModuloCosts
open _root_.ThreeSum1960614.Machine.ThreeSum.ModuloCosts
open scoped _root_.Topology

set_option maxHeartbeats 1000000















theorem maxMod_pos (n : ℕ) : 0 < _root_.ThreeSum1960614.Machine.ThreeSum.ArithmeticStageBounds.maxMod n := by
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.ArithmeticStageBounds.maxMod
  exact Nat.mul_pos (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.radix_pos n) (Nat.pow_pos (by have := _root_.ThreeSum.Scales.primeWindow_ge_two n; omega))







noncomputable section





theorem window_powerBound : _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound _root_.ThreeSum.Scales.primeWindow 0 :=
  _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound.of_rate _root_.ThreeSum1960614.Machine.ThreeSum.Scales.primeWindow_log_ratio_tendsto_zero

theorem maxMod_powerBound : _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound _root_.ThreeSum1960614.Machine.ThreeSum.ArithmeticStageBounds.maxMod (_root_.ThreeSum1960614.Machine.ThreeSum.Parameters.epsilon*(_root_.ThreeSum1960614.Machine.ThreeSum.Parameters.E+1/2)) := by
  change _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound (fun n => _root_.ThreeSum1960614.Machine.ThreeSum.Scales.radix n*(4*_root_.ThreeSum.Scales.primeWindow n)^2) (_root_.ThreeSum1960614.Machine.ThreeSum.Parameters.epsilon*(_root_.ThreeSum1960614.Machine.ThreeSum.Parameters.E+1/2))
  have hwindow := ((_root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound.const 4).mul _root_.ThreeSum1960614.Machine.ThreeSum.ArithmeticStageBounds.window_powerBound).pow 2
  have hh := (_root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound.of_rate _root_.ThreeSum1960614.Machine.ThreeSum.Scales.radix_log_ratio_tendsto).mul hwindow
  simpa only [zero_add, mul_zero, add_zero] using hh

theorem rounded_maxMod_powerBound :
    _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound (fun n => _root_.ThreeSum.ModuloCosts.roundedPower (_root_.ThreeSum1960614.Machine.ThreeSum.ArithmeticStageBounds.maxMod n)) ((8/5)*(_root_.ThreeSum1960614.Machine.ThreeSum.Parameters.epsilon*(_root_.ThreeSum1960614.Machine.ThreeSum.Parameters.E+1/2))) := by
  apply _root_.ThreeSum.ArithmeticStageBounds.powerBound_of_fifth _root_.ThreeSum1960614.Machine.ThreeSum.ArithmeticStageBounds.maxMod_powerBound
  intro n
  simpa only [show (2 : ℕ)^8 = 256 by norm_num] using _root_.ThreeSum.ModuloCosts.roundedPower_fifth (_root_.ThreeSum1960614.Machine.ThreeSum.ArithmeticStageBounds.maxMod_pos n)

theorem bitBudget_powerBound (k : ℕ) : _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound (_root_.ThreeSum.ArithmeticStageBounds.bitBudget k) 0 := by
  have hh := (_root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound.const (2*(k+2))).mul (_root_.ThreeSum1960614.Machine.ThreeSum.ArithmeticStageBounds.window_powerBound.pow 2)
  have hh' : _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound (fun n => 2*(k+2)*_root_.ThreeSum.Scales.primeWindow n^2) 0 := by
    simpa only [Nat.cast_ofNat, mul_zero, add_zero] using hh
  exact hh'.add_same (_root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound.const 1)























end
end ThreeSum.ArithmeticStageBounds

end ThreeSum1960614.Machine

section
open _root_.ThreeSum
open _root_.ThreeSum1960614.Machine.ThreeSum

open _root_.ThreeSum.ArithmeticStageBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.ArithmeticStageBounds

open _root_.Filter
open _root_.Real
open _root_.ThreeSum.Parameters
open _root_.ThreeSum1960614.Machine.ThreeSum.Parameters
open _root_.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.BandScales
open _root_.ThreeSum.CostLedger
open _root_.ThreeSum1960614.Machine.ThreeSum.CostLedger
open _root_.ThreeSum1960614.Machine.ThreeSum.HierarchyScales
open _root_.ThreeSum.MassScales
open _root_.ThreeSum1960614.Machine.ThreeSum.MassScales
open _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.UniformStageBounds
open _root_.ThreeSum.ModuloCosts
open _root_.ThreeSum1960614.Machine.ThreeSum.ModuloCosts
open scoped _root_.Topology
set_option maxHeartbeats 1000000
open _root_.ThreeSum.ArithmeticStageBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.ArithmeticStageBounds

section

theorem ThreeSum1960614.Machine.ThreeSum.ArithmeticStageBounds.perTriple_powerBound__implementation_0c5557cc56 (k : ℕ) :
    _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound (_root_.ThreeSum1960614.Machine.ThreeSum.ArithmeticStageBounds.perTripleBudget k) ((8/5)*(_root_.ThreeSum1960614.Machine.ThreeSum.Parameters.epsilon*(_root_.ThreeSum1960614.Machine.ThreeSum.Parameters.E+1/2))) := by
  change _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound (fun n => 10000*(_root_.ThreeSum.ModuloCosts.roundedPower (_root_.ThreeSum1960614.Machine.ThreeSum.ArithmeticStageBounds.maxMod n)+_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n*_root_.ThreeSum.ArithmeticStageBounds.bitBudget k n+1)) _
  have hb := (_root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound.of_rate _root_.ThreeSum1960614.Machine.ThreeSum.MassScales.bandSize_log_rate_shift).mul (_root_.ThreeSum1960614.Machine.ThreeSum.ArithmeticStageBounds.bitBudget_powerBound k)
  have hb' : _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound (fun n => _root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n*_root_.ThreeSum.ArithmeticStageBounds.bitBudget k n) (_root_.ThreeSum1960614.Machine.ThreeSum.Parameters.epsilon*(_root_.ThreeSum1960614.Machine.ThreeSum.Parameters.E+_root_.ThreeSum1960614.Machine.ThreeSum.Parameters.bandShift)) := by
    simpa only [add_zero] using hb
  have hba : _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.epsilon*(_root_.ThreeSum1960614.Machine.ThreeSum.Parameters.E+_root_.ThreeSum1960614.Machine.ThreeSum.Parameters.bandShift) ≤ (8/5)*(_root_.ThreeSum1960614.Machine.ThreeSum.Parameters.epsilon*(_root_.ThreeSum1960614.Machine.ThreeSum.Parameters.E+1/2)) := by
    have he := _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.E_bounds.1
    unfold _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.bandShift _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.epsilon
    linarith
  have hzero : (0 : ℝ) ≤ (8/5)*(_root_.ThreeSum1960614.Machine.ThreeSum.Parameters.epsilon*(_root_.ThreeSum1960614.Machine.ThreeSum.Parameters.E+1/2)) := by
    have he := _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.E_bounds.1
    unfold _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.epsilon
    linarith
  have hsum := (_root_.ThreeSum1960614.Machine.ThreeSum.ArithmeticStageBounds.rounded_maxMod_powerBound.add_same (hb'.mono_exponent hba)).add_same
    ((_root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound.const 1).mono_exponent hzero)
  have hh := (_root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound.const 10000).mul hsum
  simpa only [zero_add] using hh
end

end

theorem solution : type_of% (@ThreeSum1960614.Machine.ThreeSum.ArithmeticStageBounds.perTriple_powerBound__implementation_0c5557cc56) := (@ThreeSum1960614.Machine.ThreeSum.ArithmeticStageBounds.perTriple_powerBound__implementation_0c5557cc56)

#print axioms solution
