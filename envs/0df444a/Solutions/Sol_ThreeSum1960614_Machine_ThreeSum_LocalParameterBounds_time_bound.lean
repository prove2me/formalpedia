-- Prove2me | solution 1 for ThreeSum1960614.Machine.ThreeSum.LocalParameterBounds.time_bound
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-15T09:15:39.332008+00:00
-- url     : https://prove2.me/submissions/f2032999-d40d-46d8-9ef7-6b59eb59f046

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
import Definitions.Def_ThreeSum1960614_Machine_Bundle015
import Definitions.Def_ThreeSum1960614_Machine_Bundle016
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
import Lean
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.GCDMonoid.Nat
import Mathlib.Algebra.Group.Equiv.Basic
import Mathlib.Algebra.Group.Int.Defs
import Mathlib.Algebra.GroupWithZero.Nat
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Algebra.Order.BigOperators.Group.Multiset
import Mathlib.Algebra.Order.Floor.Div
import Mathlib.Algebra.Order.Group.Abs
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Algebra.Order.Group.Nat
import Mathlib.Algebra.Order.Group.Unbundled.Abs
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.Order.Ring.Int
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
import Mathlib.Combinatorics.Colex
import Mathlib.Data.Fin.Embedding
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Range
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Int.ModEq
import Mathlib.Data.Int.Notation
import Mathlib.Data.Int.SuccPred
import Mathlib.Data.List.Basic
import Mathlib.Data.List.GetD
import Mathlib.Data.List.MinMax
import Mathlib.Data.List.Nodup
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Data.Nat.Choose.Sum
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
import Mathlib.LinearAlgebra.Matrix.Defs
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
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
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
import Theorems.Thm_ThreeSum_LightSelectedPrime_time_bound

local instance platformRadixNonzero_c4c6ad6e93 (n : ℕ) : NeZero (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.radix n) :=
  ⟨Nat.ne_of_gt (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.radix_pos n)⟩


namespace Light
end Light
namespace ThreeSum
end ThreeSum
namespace ThreeSum.LightLocalCounts
end ThreeSum.LightLocalCounts
namespace ThreeSum.LightPascal
end ThreeSum.LightPascal
namespace ThreeSum.LightSubsetAddress
end ThreeSum.LightSubsetAddress
namespace ThreeSum.LightSubsetSetup
end ThreeSum.LightSubsetSetup
namespace ThreeSum.LocalCoverBounds
end ThreeSum.LocalCoverBounds
namespace ThreeSum.LocalParameterBounds
end ThreeSum.LocalParameterBounds
namespace ThreeSum.SubsetAddress
end ThreeSum.SubsetAddress
namespace ThreeSum1960614.Machine.Light
end ThreeSum1960614.Machine.Light
namespace ThreeSum1960614.Machine.ThreeSum
end ThreeSum1960614.Machine.ThreeSum
namespace ThreeSum1960614.Machine.ThreeSum.LightLocalCounts
end ThreeSum1960614.Machine.ThreeSum.LightLocalCounts
namespace ThreeSum1960614.Machine.ThreeSum.LightPascal
end ThreeSum1960614.Machine.ThreeSum.LightPascal
namespace ThreeSum1960614.Machine.ThreeSum.LightSubsetAddress
end ThreeSum1960614.Machine.ThreeSum.LightSubsetAddress
namespace ThreeSum1960614.Machine.ThreeSum.LightSubsetSetup
end ThreeSum1960614.Machine.ThreeSum.LightSubsetSetup
namespace ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
end ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
namespace ThreeSum1960614.Machine.ThreeSum.LocalParameterBounds
end ThreeSum1960614.Machine.ThreeSum.LocalParameterBounds
namespace ThreeSum1960614.Machine.ThreeSum.SubsetAddress
end ThreeSum1960614.Machine.ThreeSum.SubsetAddress

namespace ThreeSum1960614.Machine

/-!
# A rectangular Pascal table in the benchmark language

Every coefficient is built once by addition from the preceding row.
The row-major representation supports one multiplication and two additions
per later lookup. No recursive binomial-coefficient evaluation is used.
-/

namespace ThreeSum.LightPascal
open _root_.ThreeSum.LightPascal


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light

variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}



















theorem buildTime_bound (L : ℕ) : _root_.ThreeSum.LightPascal.buildTime L ≤ 1000*(L+1)^2 := by
  unfold _root_.ThreeSum.LightPascal.buildTime _root_.ThreeSum.LightPascal.rowTime _root_.ThreeSum.LightArray.linearTime
  simp only [_root_.Light.fillTime]
  nlinarith

end ThreeSum.LightPascal

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# A complete subset-rank program, including table construction

This fixed program constructs both lookup tables in scratch and then ranks
one valid mask. Its cost is quadratic in the bit width. The faster cached
rank contract remains available separately, but no supplied table correctness
assumption appears in the fixed-program result below.
-/

namespace ThreeSum.LightSubsetSetup
open _root_.ThreeSum.LightSubsetSetup


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.SubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.SubsetAddress
open _root_.ThreeSum.LightPascal
open _root_.ThreeSum1960614.Machine.ThreeSum.LightPascal
open _root_.ThreeSum.LightSubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.LightSubsetAddress

variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program}















theorem time_bound (L : ℕ) : _root_.ThreeSum.LightSubsetSetup.time L ≤ 1200*(L+1)^2 := by
  have hb := _root_.ThreeSum1960614.Machine.ThreeSum.LightPascal.buildTime_bound L
  unfold _root_.ThreeSum.LightSubsetSetup.time _root_.Light.powTableTime _root_.ThreeSum.LightSubsetAddress.rankTime
  nlinarith

end ThreeSum.LightSubsetSetup

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Executing the local graph counts

One constructed Pascal table and one constructed power table provide all
integer counts needed by the local hash cover. The zero-mask rank call in
the reused setup wrapper takes only linear additional time. In particular,
none of these counts is an input oracle.
-/

namespace ThreeSum.LightLocalCounts
open _root_.ThreeSum.LightLocalCounts


set_option maxHeartbeats 1000000
set_option maxRecDepth 4000

open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.LocalCoverBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
open _root_.ThreeSum.LightPascal
open _root_.ThreeSum1960614.Machine.ThreeSum.LightPascal
open _root_.ThreeSum.LightSubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.LightSubsetAddress











variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}









theorem time_bound (h : ℕ) : _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCounts.time h ≤ 1700*(464*h+1)^2 := by
  have ht := _root_.ThreeSum1960614.Machine.ThreeSum.LightSubsetSetup.time_bound (464*h)
  have hs : 0 < (464*h+1)^2 := Nat.pow_pos (by omega)
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCounts.time
  nlinarith

end ThreeSum.LightLocalCounts

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Local parameter construction fits the uniform subpolynomial budget

These bounds apply to the actual operational contracts, including the
primality scans and integer division. The deliberately loose envelope is
only used for a microblock whose half-size is a cube root of `log n`.
-/

namespace ThreeSum.LocalParameterBounds
open _root_.ThreeSum.LocalParameterBounds


open _root_.ThreeSum.LocalCoverBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds

set_option maxHeartbeats 1000000




theorem pow_pos (e : ℕ) : 1 ≤ (2 : ℕ)^e := Nat.pos_iff_ne_zero.mpr (pow_ne_zero _ (by decide))

theorem threshold_bound (h : ℕ) : _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localThreshold h ≤ 2^(514*h) := by
  calc
    _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localThreshold h ≤ 2^(464*h)*2^(2*h) :=
      Nat.mul_le_mul_right _ (Nat.choose_le_two_pow _ _)
    _ ≤ 2^(514*h) := by
      rw [← pow_add]
      exact Nat.pow_le_pow_right (by decide) (by omega)

theorem vertex_bound (h : ℕ) : _root_.ThreeSum.LocalCoverBounds.vertexCount (464*h) h ≤ 2^(514*h) :=
  (Nat.choose_le_two_pow _ _).trans (Nat.pow_le_pow_right (by decide) (by omega))

theorem root_bound (h : ℕ) : _root_.ThreeSum.LocalCoverBounds.rootCeiling (_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localThreshold h) ≤ 2*2^(514*h) := by
  have hs := Nat.sqrt_le_self (_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localThreshold h-1)
  have ht := _root_.ThreeSum1960614.Machine.ThreeSum.LocalParameterBounds.threshold_bound h
  have hp := _root_.ThreeSum1960614.Machine.ThreeSum.LocalParameterBounds.pow_pos (514*h)
  unfold _root_.ThreeSum.LocalCoverBounds.rootCeiling
  omega

theorem prime_bound (h : ℕ) : _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime h ≤ 2^(514*h+2) := by
  have hp := (_root_.ThreeSum.LocalCoverBounds.selectedPrime_spec (_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localThreshold h)).2.2
  have hr := _root_.ThreeSum1960614.Machine.ThreeSum.LocalParameterBounds.root_bound h
  change _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime h ≤ _ at hp
  rw [pow_add]
  norm_num
  omega

theorem width_bound (h : ℕ) : 464*h+1 ≤ 2^(h+10) := by
  have hh : h < 2^h := Nat.lt_two_pow_self
  have hp := _root_.ThreeSum1960614.Machine.ThreeSum.LocalParameterBounds.pow_pos h
  rw [pow_add]
  norm_num
  omega

theorem count_time_bound (h : ℕ) : _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCounts.time h ≤ 2^(2*h+31) := by
  calc
    _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCounts.time h ≤ 1700*(464*h+1)^2 := _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCounts.time_bound h
    _ ≤ 2^11*(2^(h+10))^2 := Nat.mul_le_mul (by decide) (Nat.pow_le_pow_left (_root_.ThreeSum1960614.Machine.ThreeSum.LocalParameterBounds.width_bound h) 2)
    _ = 2^(2*h+31) := by rw [← pow_mul,← pow_add]; congr 1 <;> omega

theorem selected_time_bound (h : ℕ) :
    _root_.ThreeSum.LightSelectedPrime.time (_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localThreshold h) ≤ 2^(1542*h+19) := by
  have ht := _root_.ThreeSum1960614.Machine.ThreeSum.LocalParameterBounds.threshold_bound h
  have hx := _root_.ThreeSum1960614.Machine.ThreeSum.LocalParameterBounds.pow_pos (514*h)
  have ha : _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localThreshold h+2 ≤ 2^(514*h+2) := by
    rw [pow_add]
    norm_num
    omega
  calc
    _ ≤ 6000*(_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localThreshold h+2)^3 := _root_.ThreeSum.LightSelectedPrime.time_bound _
    _ ≤ 2^13*(2^(514*h+2))^3 := Nat.mul_le_mul (by decide) (Nat.pow_le_pow_left ha 3)
    _ = 2^(1542*h+19) := by rw [← pow_mul,← pow_add]; congr 1 <;> omega

theorem cap_time_bound (h : ℕ) :
    _root_.ThreeSum.LightSmallDivide.time (_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalParameters.numerator h) (_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime h) ≤ 2^(514*h+10) := by
  have hp := _root_.ThreeSum1960614.Machine.ThreeSum.LocalParameterBounds.prime_bound h
  have hv := _root_.ThreeSum1960614.Machine.ThreeSum.LocalParameterBounds.vertex_bound h
  have hx := _root_.ThreeSum1960614.Machine.ThreeSum.LocalParameterBounds.pow_pos (514*h)
  rw [pow_add] at hp
  norm_num at hp
  have hn : _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalParameters.numerator h ≤ 24*2^(514*h) := by
    unfold _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalParameters.numerator
    omega
  have hq := Nat.div_le_self (_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalParameters.numerator h) (_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime h)
  unfold _root_.ThreeSum.LightSmallDivide.time
  rw [pow_add]
  norm_num
  omega





















end ThreeSum.LocalParameterBounds

end ThreeSum1960614.Machine

section
open _root_.ThreeSum
open _root_.ThreeSum1960614.Machine.ThreeSum

open _root_.ThreeSum.LocalParameterBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.LocalParameterBounds

open _root_.ThreeSum.LocalCoverBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
set_option maxHeartbeats 1000000
section

theorem ThreeSum1960614.Machine.ThreeSum.LocalParameterBounds.time_bound__implementation_17d4a7ee90 (h : ℕ) : _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalParameters.time h ≤ _root_.ThreeSum.LocalParameterBounds.envelope h := by
  have hc : _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCounts.time h ≤ _root_.ThreeSum.LocalParameterBounds.base h :=
    (_root_.ThreeSum1960614.Machine.ThreeSum.LocalParameterBounds.count_time_bound h).trans (Nat.pow_le_pow_right (by decide) (by omega))
  have hp : _root_.ThreeSum.LightSelectedPrime.time (_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localThreshold h) ≤ _root_.ThreeSum.LocalParameterBounds.base h :=
    (_root_.ThreeSum1960614.Machine.ThreeSum.LocalParameterBounds.selected_time_bound h).trans (Nat.pow_le_pow_right (by decide) (by omega))
  have hd : _root_.ThreeSum.LightSmallDivide.time (_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalParameters.numerator h) (_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime h) ≤ _root_.ThreeSum.LocalParameterBounds.base h :=
    (_root_.ThreeSum1960614.Machine.ThreeSum.LocalParameterBounds.cap_time_bound h).trans (Nat.pow_le_pow_right (by decide) (by omega))
  have hk : 200 ≤ _root_.ThreeSum.LocalParameterBounds.base h := (by decide : 200 ≤ 2^8).trans
    (Nat.pow_le_pow_right (by decide) (by omega))
  have he : _root_.ThreeSum.LocalParameterBounds.envelope h = 4*_root_.ThreeSum.LocalParameterBounds.base h := by unfold _root_.ThreeSum.LocalParameterBounds.envelope _root_.ThreeSum.LocalParameterBounds.base; rw [pow_add]; norm_num; omega
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalParameters.time
  rw [he]
  omega
end

end

theorem solution : type_of% (@ThreeSum1960614.Machine.ThreeSum.LocalParameterBounds.time_bound__implementation_17d4a7ee90) := (@ThreeSum1960614.Machine.ThreeSum.LocalParameterBounds.time_bound__implementation_17d4a7ee90)

#print axioms solution
