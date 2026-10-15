-- Prove2me | solution 1 for ThreeSum1960614.Machine.ThreeSum.MassScales.falseNumerator_log_rate
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-15T09:14:52.922434+00:00
-- url     : https://prove2.me/submissions/e990cad5-baf7-4083-9f92-eb1652833e1e

import Aesop
import Definitions.Def_APSPSource_RemainingDefinitions
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Syntax
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
import Definitions.Def_ThreeSum1960614_Machine_Bundle012
import Definitions.Def_ThreeSum1960614_Machine_Bundle014
import Definitions.Def_ThreeSum1960614_Machine_Bundle016
import Definitions.Def_ThreeSum1960614_Machine_Bundle018
import Definitions.Def_ThreeSum1962Source_Bundle01
import Definitions.Def_ThreeSum1962Source_Bundle04
import Definitions.Def_ThreeSum1962Source_Bundle05
import Definitions.Def_ThreeSum1962Source_Bundle07
import Definitions.Def_ThreeSum1962Source_Bundle09
import Lean
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Group.Int.Defs
import Mathlib.Algebra.GroupWithZero.Nat
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Floor.Div
import Mathlib.Algebra.Order.Group.Abs
import Mathlib.Algebra.Order.Group.Unbundled.Abs
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.Order.Ring.Pow
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
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.List.MinMax
import Mathlib.Data.List.Pi
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.Index
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Matrix.Dual
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.NumberTheory.Bertrand
import Mathlib.NumberTheory.Chebyshev
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Order.Monotone.Basic
import Mathlib.Tactic
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
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_BandScales_bandSize_log_rate
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_HierarchyScales_bandCount_log_rate
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_Scales_primeLoss_log_ratio_tendsto_zero
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_Scales_scoreLoss_log_ratio_tendsto_zero
import Theorems.Thm_ThreeSum_MassScales_candidateCount_log_rate

local instance platformRadixNonzero_7056168263 (n : ℕ) : NeZero (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.radix n) :=
  ⟨Nat.ne_of_gt (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.radix_pos n)⟩


namespace Filter
end Filter
namespace Real
end Real
namespace Set
end Set
namespace ThreeSum
end ThreeSum
namespace ThreeSum.CostLedger
end ThreeSum.CostLedger
namespace ThreeSum.MassScales
end ThreeSum.MassScales
namespace ThreeSum.Parameters
end ThreeSum.Parameters
namespace ThreeSum.Scales
end ThreeSum.Scales
namespace ThreeSum1960614.Machine.ThreeSum
end ThreeSum1960614.Machine.ThreeSum
namespace ThreeSum1960614.Machine.ThreeSum.BandScales
end ThreeSum1960614.Machine.ThreeSum.BandScales
namespace ThreeSum1960614.Machine.ThreeSum.CostLedger
end ThreeSum1960614.Machine.ThreeSum.CostLedger
namespace ThreeSum1960614.Machine.ThreeSum.HierarchyScales
end ThreeSum1960614.Machine.ThreeSum.HierarchyScales
namespace ThreeSum1960614.Machine.ThreeSum.MassScales
end ThreeSum1960614.Machine.ThreeSum.MassScales
namespace ThreeSum1960614.Machine.ThreeSum.Parameters
end ThreeSum1960614.Machine.ThreeSum.Parameters
namespace ThreeSum1960614.Machine.ThreeSum.Scales
end ThreeSum1960614.Machine.ThreeSum.Scales
namespace ThreeSum1960614.Machine.ThreeSum.Switch
end ThreeSum1960614.Machine.ThreeSum.Switch
namespace ThreeSum1960614.Machine.ThreeSum.TrimScales
end ThreeSum1960614.Machine.ThreeSum.TrimScales

namespace ThreeSum1960614.Machine

/-!
# Actual finite hierarchy counts

These are the binomial counts used by the concrete microblock hierarchy.
Every prefix partition is included.  The integer switch and its rounding
allowance are applied before any asymptotic estimate is made.  The counts
in this module are combinatorial work counts; the implementation's operation
counts, raw wanted incidences, and false-mass bounds are separate interfaces.
-/

namespace ThreeSum.CostLedger
open _root_.ThreeSum.CostLedger


open _root_.Filter
open _root_.Set
open _root_.Real
open _root_.ThreeSum.Parameters
open _root_.ThreeSum1960614.Machine.ThreeSum.Parameters
open _root_.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.Switch
open scoped _root_.Topology
open scoped _root_.BigOperators

set_option maxHeartbeats 400000



















theorem bandCount_mul_bounds (n : ℕ) :
    n ≤ _root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n * _root_.ThreeSum1960614.Machine.ThreeSum.CostLedger.bandCount n ∧
      _root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n * _root_.ThreeSum1960614.Machine.ThreeSum.CostLedger.bandCount n < n + _root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n := by
  constructor
  · exact (ceilDiv_le_iff_le_mul (a := _root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n) (b := n)
      (c := _root_.ThreeSum1960614.Machine.ThreeSum.CostLedger.bandCount n) (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize_pos n)).mp le_rfl
  · have h := Nat.div_mul_le_self (n + _root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n - 1) (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n)
    simp only [_root_.ThreeSum1960614.Machine.ThreeSum.CostLedger.bandCount, Nat.ceilDiv_eq_add_pred_div]
    rw [Nat.mul_comm (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n)]
    have hpos := _root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize_pos n
    omega











noncomputable section















end
end ThreeSum.CostLedger

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









theorem bandCount_pos {n : ℕ} (hn : 0 < n) : 0 < _root_.ThreeSum1960614.Machine.ThreeSum.CostLedger.bandCount n :=
  Nat.pos_of_mul_pos_left (hn.trans_le (_root_.ThreeSum1960614.Machine.ThreeSum.CostLedger.bandCount_mul_bounds n).1)

theorem rawTripleBound_pos {n : ℕ} (hn : 0 < n) : 0 < _root_.ThreeSum1960614.Machine.ThreeSum.MassScales.rawTripleBound n := by
  have hB := _root_.ThreeSum1960614.Machine.ThreeSum.MassScales.bandCount_pos hn
  have hb := _root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize_pos n
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.MassScales.rawTripleBound
  positivity



theorem scoreLoss_pos (k n : ℕ) : 0 < _root_.ThreeSum1960614.Machine.ThreeSum.Scales.scoreLoss k n := by
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.Scales.scoreLoss
  positivity

theorem primeLoss_pos (n : ℕ) : 0 < _root_.ThreeSum.Scales.primeLoss _root_.ThreeSum1960614.Machine.ThreeSum.Scales.radix n := by
  have hy := _root_.ThreeSum.Scales.primeWindow_ge_two n
  unfold _root_.ThreeSum.Scales.primeLoss
  positivity

theorem candidateCount_eventually_pos : ∀ᶠ n : ℕ in atTop, 0 < _root_.ThreeSum.Scales.candidateCount n := by
  filter_upwards [_root_.ThreeSum.Scales.actual_candidates_nonempty] with n hn
  exact Finset.card_pos.mpr hn



noncomputable section





theorem nat_log_rate_const (c : ℕ) :
    Tendsto (fun n : ℕ => Real.log (c : ℝ) / Real.log n) atTop (𝓝 0) := by
  simpa only [mul_zero, Pi.inv_apply, div_eq_mul_inv] using
    _root_.ThreeSum.Asymptotics.log_nat_tendsto_atTop.inv_tendsto_atTop.const_mul (Real.log (c : ℝ))

theorem nat_log_rate_mul {f g : ℕ → ℕ} {a b : ℝ}
    (hf : Tendsto (fun n : ℕ => Real.log (f n : ℝ) / Real.log n) atTop (𝓝 a))
    (hg : Tendsto (fun n : ℕ => Real.log (g n : ℝ) / Real.log n) atTop (𝓝 b))
    (hp : ∀ᶠ n : ℕ in atTop, 0 < f n ∧ 0 < g n) :
    Tendsto (fun n : ℕ => Real.log ((f n * g n : ℕ) : ℝ) / Real.log n) atTop (𝓝 (a + b)) := by
  apply (hf.add hg).congr'
  filter_upwards [hp] with n hn
  have hfR : (f n : ℝ) ≠ 0 := by exact_mod_cast hn.1.ne'
  have hgR : (g n : ℝ) ≠ 0 := by exact_mod_cast hn.2.ne'
  simp only [Nat.cast_mul, Real.log_mul hfR hgR, add_div]

theorem nat_log_rate_pow {f : ℕ → ℕ} {a : ℝ}
    (hf : Tendsto (fun n : ℕ => Real.log (f n : ℝ) / Real.log n) atTop (𝓝 a)) (k : ℕ) :
    Tendsto (fun n : ℕ => Real.log ((f n ^ k : ℕ) : ℝ) / Real.log n) atTop (𝓝 ((k : ℝ) * a)) := by
  simpa only [Nat.cast_pow, Real.log_pow, mul_div_assoc] using hf.const_mul (k : ℝ)





theorem bandSize_log_rate_shift :
    Tendsto (fun n : ℕ => Real.log (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n : ℝ) / Real.log n) atTop
      (𝓝 (_root_.ThreeSum1960614.Machine.ThreeSum.Parameters.epsilon * (_root_.ThreeSum1960614.Machine.ThreeSum.Parameters.E + _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.bandShift))) := by
  simpa only [_root_.ThreeSum1960614.Machine.ThreeSum.Parameters.bandShift, sub_eq_add_neg] using _root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize_log_rate



theorem rawTripleBound_log_rate :
    Tendsto (fun n : ℕ => Real.log (_root_.ThreeSum1960614.Machine.ThreeSum.MassScales.rawTripleBound n : ℝ) / Real.log n) atTop
      (𝓝 (2 + _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.epsilon * (_root_.ThreeSum1960614.Machine.ThreeSum.Parameters.E + _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.bandShift))) := by
  have h1 := _root_.ThreeSum1960614.Machine.ThreeSum.MassScales.nat_log_rate_mul (_root_.ThreeSum1960614.Machine.ThreeSum.MassScales.nat_log_rate_const 3) (_root_.ThreeSum1960614.Machine.ThreeSum.MassScales.nat_log_rate_pow _root_.ThreeSum1960614.Machine.ThreeSum.HierarchyScales.bandCount_log_rate 2) (by
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
    exact ⟨by norm_num, Nat.pow_pos (_root_.ThreeSum1960614.Machine.ThreeSum.MassScales.bandCount_pos (by omega))⟩)
  have h2 := _root_.ThreeSum1960614.Machine.ThreeSum.MassScales.nat_log_rate_mul h1 (_root_.ThreeSum1960614.Machine.ThreeSum.MassScales.nat_log_rate_pow _root_.ThreeSum1960614.Machine.ThreeSum.MassScales.bandSize_log_rate_shift 3) (by
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
    exact ⟨Nat.mul_pos (by norm_num) (Nat.pow_pos (_root_.ThreeSum1960614.Machine.ThreeSum.MassScales.bandCount_pos (by omega))),
      Nat.pow_pos (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize_pos n)⟩)
  convert h2 using 1 <;> simp only [_root_.ThreeSum1960614.Machine.ThreeSum.MassScales.rawTripleBound, Nat.cast_ofNat] <;> ring















end
end ThreeSum.MassScales

end ThreeSum1960614.Machine

section
open _root_.ThreeSum
open _root_.ThreeSum1960614.Machine.ThreeSum

open _root_.ThreeSum.MassScales
open _root_.ThreeSum1960614.Machine.ThreeSum.MassScales

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
open _root_.ThreeSum.MassScales
open _root_.ThreeSum1960614.Machine.ThreeSum.MassScales

section

theorem ThreeSum1960614.Machine.ThreeSum.MassScales.falseNumerator_log_rate__implementation_50ed84782b (k : ℕ) :
    Tendsto (fun n : ℕ => Real.log (_root_.ThreeSum1960614.Machine.ThreeSum.MassScales.falseNumerator k n : ℝ) / Real.log n) atTop
      (𝓝 (2 + _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.epsilon * (_root_.ThreeSum1960614.Machine.ThreeSum.Parameters.E + _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.bandShift))) := by
  have h1 := _root_.ThreeSum1960614.Machine.ThreeSum.MassScales.nat_log_rate_mul _root_.ThreeSum.MassScales.candidateCount_log_rate _root_.ThreeSum1960614.Machine.ThreeSum.MassScales.rawTripleBound_log_rate (by
    filter_upwards [_root_.ThreeSum1960614.Machine.ThreeSum.MassScales.candidateCount_eventually_pos, eventually_ge_atTop (1 : ℕ)] with n hC hn
    exact ⟨hC, _root_.ThreeSum1960614.Machine.ThreeSum.MassScales.rawTripleBound_pos (by omega)⟩)
  have h2 := _root_.ThreeSum1960614.Machine.ThreeSum.MassScales.nat_log_rate_mul h1 (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.scoreLoss_log_ratio_tendsto_zero k) (by
    filter_upwards [_root_.ThreeSum1960614.Machine.ThreeSum.MassScales.candidateCount_eventually_pos, eventually_ge_atTop (1 : ℕ)] with n hC hn
    exact ⟨Nat.mul_pos hC (_root_.ThreeSum1960614.Machine.ThreeSum.MassScales.rawTripleBound_pos (by omega)), _root_.ThreeSum1960614.Machine.ThreeSum.MassScales.scoreLoss_pos k n⟩)
  have h3 := _root_.ThreeSum1960614.Machine.ThreeSum.MassScales.nat_log_rate_mul h2 _root_.ThreeSum1960614.Machine.ThreeSum.Scales.primeLoss_log_ratio_tendsto_zero (by
    filter_upwards [_root_.ThreeSum1960614.Machine.ThreeSum.MassScales.candidateCount_eventually_pos, eventually_ge_atTop (1 : ℕ)] with n hC hn
    exact ⟨Nat.mul_pos (Nat.mul_pos hC (_root_.ThreeSum1960614.Machine.ThreeSum.MassScales.rawTripleBound_pos (by omega))) (_root_.ThreeSum1960614.Machine.ThreeSum.MassScales.scoreLoss_pos k n),
      _root_.ThreeSum1960614.Machine.ThreeSum.MassScales.primeLoss_pos n⟩)
  simpa only [_root_.ThreeSum1960614.Machine.ThreeSum.MassScales.falseNumerator, zero_add, add_zero] using h3
end

end

theorem solution : type_of% (@ThreeSum1960614.Machine.ThreeSum.MassScales.falseNumerator_log_rate__implementation_50ed84782b) := (@ThreeSum1960614.Machine.ThreeSum.MassScales.falseNumerator_log_rate__implementation_50ed84782b)

#print axioms solution
