-- Prove2me | solution 1 for ThreeSum1960614.Machine.ThreeSum.ThreeSumFastResources.poly_need
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-15T09:21:14.149149+00:00
-- url     : https://prove2.me/submissions/1dfe4bfc-6936-4a9b-83a1-df965469498d

import Aesop
import Definitions.Def_APSPSource_PaperStatements
import Definitions.Def_APSPSource_RemainingDefinitions
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Regions
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Syntax
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_WordSize
import Definitions.Def_APSPSource_ThreeSumApsp_Util_Index
import Definitions.Def_APSPSource_ThreeSumApsp_Util_List
import Definitions.Def_ThreeSum1960614_Analysis
import Definitions.Def_ThreeSum1960614_Machine_Bundle001
import Definitions.Def_ThreeSum1960614_Machine_Bundle002
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
import Definitions.Def_ThreeSum1960614_Machine_Bundle015
import Definitions.Def_ThreeSum1960614_Machine_Bundle016
import Definitions.Def_ThreeSum1960614_Machine_Bundle017
import Definitions.Def_ThreeSum1960614_Machine_Bundle018
import Definitions.Def_ThreeSum1960614_Machine_Bundle019
import Definitions.Def_ThreeSum1960614_Machine_Bundle020
import Definitions.Def_ThreeSum1960614_Machine_Bundle021
import Definitions.Def_ThreeSum1960614_Machine_Bundle022
import Definitions.Def_ThreeSum1960614_Machine_Bundle023
import Definitions.Def_ThreeSum1960614_Machine_Bundle024
import Definitions.Def_ThreeSum1960614_Machine_Bundle025
import Definitions.Def_ThreeSum1960614_Machine_Bundle026
import Definitions.Def_ThreeSum1960614_Machine_Bundle027
import Definitions.Def_ThreeSum1960614_Machine_Bundle028
import Definitions.Def_ThreeSum1960614_Machine_Bundle029
import Definitions.Def_ThreeSum1960614_Machine_Bundle030
import Definitions.Def_ThreeSum1960614_Machine_Bundle031
import Definitions.Def_ThreeSum1960614_Machine_Bundle032
import Definitions.Def_ThreeSum1960614_Machine_Bundle033
import Definitions.Def_ThreeSum1960614_Machine_Bundle034
import Definitions.Def_ThreeSum1960614_Machine_Bundle035
import Definitions.Def_ThreeSum1960614_Machine_Bundle036
import Definitions.Def_ThreeSum1960614_Machine_Bundle037
import Definitions.Def_ThreeSum1960614_Machine_Bundle038
import Definitions.Def_ThreeSum1960614_Machine_Bundle039
import Definitions.Def_ThreeSum1960614_Machine_Bundle040
import Definitions.Def_ThreeSum1962Source_Bundle01
import Definitions.Def_ThreeSum1962Source_Bundle02
import Definitions.Def_ThreeSum1962Source_Bundle03
import Definitions.Def_ThreeSum1962Source_Bundle04
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
import Lean
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
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
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
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.Tauto
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
import Theorems.Thm_ThreeSum_PolynomialResources_pair_polyBound_of_powerBound
import Theorems.Thm_ThreeSum_StageBounds_PowerBound_add_same

private theorem ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound.add_same {f g : ℕ → ℕ} {a : ℝ}
    (hf : _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound f a)
    (hg : _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound g a) :
    _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound (fun n => f n+g n) a := by
  exact _root_.ThreeSum.StageBounds.PowerBound.add_same hf hg


local instance platformRadixNonzero_186564c25a (n : ℕ) : NeZero (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.radix n) :=
  ⟨Nat.ne_of_gt (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.radix_pos n)⟩


namespace Filter
end Filter
namespace Light
end Light
namespace Real
end Real
namespace ThreeSum
end ThreeSum
namespace ThreeSum.ArithmeticStageBounds
end ThreeSum.ArithmeticStageBounds
namespace ThreeSum.CostLedger
end ThreeSum.CostLedger
namespace ThreeSum.LocalCoverBounds
end ThreeSum.LocalCoverBounds
namespace ThreeSum.MassScales
end ThreeSum.MassScales
namespace ThreeSum.ModuloCosts
end ThreeSum.ModuloCosts
namespace ThreeSum.Parameters
end ThreeSum.Parameters
namespace ThreeSum.PolynomialResources
end ThreeSum.PolynomialResources
namespace ThreeSum.ReportingHostWantedLayout
end ThreeSum.ReportingHostWantedLayout
namespace ThreeSum.Scales
end ThreeSum.Scales
namespace ThreeSum.SharedReportingBankResourceBounds
end ThreeSum.SharedReportingBankResourceBounds
namespace ThreeSum.StageBounds
end ThreeSum.StageBounds
namespace ThreeSum.StageBounds.PowerBound
end ThreeSum.StageBounds.PowerBound
namespace ThreeSum.ThreeSumFastResources
end ThreeSum.ThreeSumFastResources
namespace ThreeSum1960614.Machine.Light
end ThreeSum1960614.Machine.Light
namespace ThreeSum1960614.Machine.ThreeSum
end ThreeSum1960614.Machine.ThreeSum
namespace ThreeSum1960614.Machine.ThreeSum.ArithmeticStageBounds
end ThreeSum1960614.Machine.ThreeSum.ArithmeticStageBounds
namespace ThreeSum1960614.Machine.ThreeSum.BandScales
end ThreeSum1960614.Machine.ThreeSum.BandScales
namespace ThreeSum1960614.Machine.ThreeSum.CostLedger
end ThreeSum1960614.Machine.ThreeSum.CostLedger
namespace ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
end ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
namespace ThreeSum1960614.Machine.ThreeSum.HierarchyScales
end ThreeSum1960614.Machine.ThreeSum.HierarchyScales
namespace ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
end ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
namespace ThreeSum1960614.Machine.ThreeSum.MassScales
end ThreeSum1960614.Machine.ThreeSum.MassScales
namespace ThreeSum1960614.Machine.ThreeSum.ModuloCosts
end ThreeSum1960614.Machine.ThreeSum.ModuloCosts
namespace ThreeSum1960614.Machine.ThreeSum.Parameters
end ThreeSum1960614.Machine.ThreeSum.Parameters
namespace ThreeSum1960614.Machine.ThreeSum.PolynomialResources
end ThreeSum1960614.Machine.ThreeSum.PolynomialResources
namespace ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedLayout
end ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedLayout
namespace ThreeSum1960614.Machine.ThreeSum.Scales
end ThreeSum1960614.Machine.ThreeSum.Scales
namespace ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout
end ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout
namespace ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds
end ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds
namespace ThreeSum1960614.Machine.ThreeSum.StageBounds
end ThreeSum1960614.Machine.ThreeSum.StageBounds
namespace ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound
end ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound
namespace ThreeSum1960614.Machine.ThreeSum.Switch
end ThreeSum1960614.Machine.ThreeSum.Switch
namespace ThreeSum1960614.Machine.ThreeSum.ThreeSumFastResources
end ThreeSum1960614.Machine.ThreeSum.ThreeSumFastResources
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























noncomputable section

theorem powerBound_mono {f g : ℕ → ℕ} {a : ℝ} (hg : _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound g a)
    (hfg : ∀ᶠ n : ℕ in atTop, f n ≤ g n) : _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound f a := by
  intro d hd
  filter_upwards [hg d hd, hfg] with n hn hm
  exact (show (f n : ℝ) ≤ (g n : ℝ) by exact_mod_cast hm).trans hn

















theorem identity_powerBound : _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound (fun n : ℕ => n) 1 := by
  intro d hd
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  simpa only [Real.rpow_one] using
    (Real.rpow_le_rpow_of_exponent_le hnR (show (1 : ℝ) ≤ 1+d by linarith))















end
end ThreeSum.ArithmeticStageBounds

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# From proved resource envelopes to the compiler's polynomial limits

An eventual power bound supplies a single polynomial valid at every input
size, by explicitly absorbing its finitely many exceptions. Multiplying
by a fixed power of the input magnitude then gives the exact two-parameter
`Light.PolyNeed` required by the verified compiler. These lemmas do not
supply resource envelopes for an algorithm; callers must prove those.
-/

namespace ThreeSum.PolynomialResources
open _root_.ThreeSum.PolynomialResources


open _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds
open _root_.Filter
open _root_.Real
open scoped _root_.Topology

noncomputable section







theorem polyNeed_of_envelope {need : ℕ → ℕ → _root_.ThreeSum1960614.Machine.Light.Need} {f : ℕ → ℕ} {a : ℝ}
    (hf : _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound f a) (e : ℕ)
    (hword : ∀ n U, (need n U).word ≤ f n*(U+1)^e)
    (hcells : ∀ n U, (need n U).cells ≤ f n*(U+1)^e)
    (hdepth : ∀ n U, (need n U).depth ≤ f n*(U+1)^e) : _root_.ThreeSum1960614.Machine.Light.PolyNeed need := by
  obtain ⟨s,k,h⟩ := _root_.ThreeSum.PolynomialResources.pair_polyBound_of_powerBound hf e
  exact ⟨s,k,fun n U => ⟨(hword n U).trans (h n U),
    (hcells n U).trans (h n U),(hdepth n U).trans (h n U)⟩⟩



end
end ThreeSum.PolynomialResources

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Polynomial limits for the actual shared reporting host

The finite word, cell, and depth formulas are bounded at every input size.
The resulting `Need` includes the complete executed host, while its time
bound remains the exact shared-box budget proved separately.
-/

namespace ThreeSum.SharedReportingBankResourceBounds
open _root_.ThreeSum.SharedReportingBankResourceBounds


open _root_.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds
open _root_.Filter
open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open scoped _root_.Topology

set_option maxHeartbeats 1200000
set_option maxRecDepth 14000

noncomputable section

theorem bits_power_powerBound : _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound (fun n => 2^(_root_.ThreeSum.Scales.inputBits n)) 1 := by
  apply _root_.ThreeSum1960614.Machine.ThreeSum.ArithmeticStageBounds.powerBound_mono _root_.ThreeSum1960614.Machine.ThreeSum.ArithmeticStageBounds.identity_powerBound
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
  simpa only [_root_.ThreeSum.Scales.inputBits,Nat.log2_eq_log_two] using
    Nat.pow_log_le_self 2 (by omega : n ≠ 0)

theorem magnitude_powerBound : _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound _root_.ThreeSum.SharedReportingBankResourceBounds.magnitude 2048 := by
  have hh := (_root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound.const (2^2048)).mul (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.bits_power_powerBound.pow 2048)
  have he : _root_.ThreeSum.SharedReportingBankResourceBounds.magnitude = fun n => 2^2048*(2^(_root_.ThreeSum.Scales.inputBits n))^2048 := by
    funext n
    unfold _root_.ThreeSum.SharedReportingBankResourceBounds.magnitude
    rw [show 2048*(_root_.ThreeSum.Scales.inputBits n+1)=2048+_root_.ThreeSum.Scales.inputBits n*2048 by omega,pow_add,pow_mul]
  rw [he]
  simpa only [Nat.cast_ofNat,mul_one,zero_add] using hh

















end
end ThreeSum.SharedReportingBankResourceBounds

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-! # Polynomial relative resources for every physical wanted slot -/

namespace ThreeSum.SharedReportingBankResourceBounds
open _root_.ThreeSum.SharedReportingBankResourceBounds


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
open _root_.ThreeSum.LocalCoverBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout
open _root_.ThreeSum.ReportingHostWantedLayout
open _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedLayout

set_option maxHeartbeats 3200000
set_option maxRecDepth 16000





theorem wanted_power_le (n e f : ℕ) (hef : e≤f) :
    (_root_.ThreeSum.SharedReportingBankResourceBounds.magnitude n)^e≤(_root_.ThreeSum.SharedReportingBankResourceBounds.magnitude n+1)^f :=
  (Nat.pow_le_pow_left (Nat.le_succ _) e).trans (Nat.pow_le_pow_right (by omega) hef)















theorem wanted_envelope_positive (n : ℕ) : 2≤_root_.ThreeSum.SharedReportingBankResourceBounds.wantedEnvelope n := by
  have h1 : 1≤(_root_.ThreeSum.SharedReportingBankResourceBounds.magnitude n+1)^10 := Nat.one_le_pow _ _ (by omega)
  unfold _root_.ThreeSum.SharedReportingBankResourceBounds.wantedEnvelope
  omega

noncomputable section

theorem wanted_envelope_powerBound : _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound _root_.ThreeSum.SharedReportingBankResourceBounds.wantedEnvelope 20480 := by
  have hm := _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.magnitude_powerBound.add_same
    ((_root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound.const 1).mono_exponent (by norm_num : (0 : ℝ)≤2048))
  have hh := (_root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound.const 10000).mul (hm.pow 10)
  convert hh using 1 <;> (first | rfl | norm_num [_root_.ThreeSum.SharedReportingBankResourceBounds.wantedEnvelope])











end
end ThreeSum.SharedReportingBankResourceBounds

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-! # Polynomial call depth for scanning every physical wanted record

The scan retains the exact word and cell reservations of one wanted
dispatcher. Only its depth includes the number of physical records.
-/

namespace ThreeSum.SharedReportingBankResourceBounds
open _root_.ThreeSum.SharedReportingBankResourceBounds


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds

set_option maxHeartbeats 1700000
set_option maxRecDepth 14000







theorem wanted_scan_count_envelope (n : ℕ) : _root_.ThreeSum.SharedReportingBankResourceBounds.wantedScanCount n+4≤_root_.ThreeSum.SharedReportingBankResourceBounds.wantedEnvelope n := by
  have h5 := _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.wanted_power_le n 5 10 (by decide)
  have h1 : 1≤(_root_.ThreeSum.SharedReportingBankResourceBounds.magnitude n+1)^10 := Nat.one_le_pow _ _ (by omega)
  unfold _root_.ThreeSum.SharedReportingBankResourceBounds.wantedScanCount _root_.ThreeSum.SharedReportingBankResourceBounds.wantedEnvelope
  omega







noncomputable section



end
end ThreeSum.SharedReportingBankResourceBounds

end ThreeSum1960614.Machine

section
open _root_.ThreeSum
open _root_.ThreeSum1960614.Machine.ThreeSum

open _root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumFastResources

open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.BandScales
open _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds
open _root_.ThreeSum.SharedReportingBankResourceBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds
set_option maxHeartbeats 2100000
set_option maxRecDepth 15000
open _root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumFastResources

section

theorem ThreeSum1960614.Machine.ThreeSum.ThreeSumFastResources.poly_need__implementation_873298c67a : _root_.ThreeSum1960614.Machine.Light.PolyNeed _root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumFastResources.need := by
  have he : _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound (fun n => 3*_root_.ThreeSum.SharedReportingBankResourceBounds.wantedEnvelope n) 20480 := by
    simpa only [zero_add] using (_root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound.const 3).mul _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.wanted_envelope_powerBound
  apply _root_.ThreeSum1960614.Machine.ThreeSum.PolynomialResources.polyNeed_of_envelope he 1
  · intro n U
    simp only [_root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumFastResources.need,_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.wantedScanNeed,_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.wantedNeed,pow_one]
    nlinarith only [Nat.zero_le (_root_.ThreeSum.SharedReportingBankResourceBounds.wantedEnvelope n*(U+1))]
  · intro n U
    simp only [_root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumFastResources.need,_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.wantedScanNeed,_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.wantedNeed,pow_one]
    have hh : _root_.ThreeSum.SharedReportingBankResourceBounds.wantedEnvelope n≤_root_.ThreeSum.SharedReportingBankResourceBounds.wantedEnvelope n*(U+1) := Nat.le_mul_of_pos_right _ (by omega)
    nlinarith only [hh]
  · intro n U
    simp only [_root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumFastResources.need,_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.wantedScanNeed,_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.wantedNeed,pow_one]
    have hc := _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.wanted_scan_count_envelope n
    have hp := _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.wanted_envelope_positive n
    have hh : 3*_root_.ThreeSum.SharedReportingBankResourceBounds.wantedEnvelope n≤3*_root_.ThreeSum.SharedReportingBankResourceBounds.wantedEnvelope n*(U+1) := Nat.le_mul_of_pos_right _ (by omega)
    omega
end

end

theorem solution : type_of% (@ThreeSum1960614.Machine.ThreeSum.ThreeSumFastResources.poly_need__implementation_873298c67a) := (@ThreeSum1960614.Machine.ThreeSum.ThreeSumFastResources.poly_need__implementation_873298c67a)

#print axioms solution
