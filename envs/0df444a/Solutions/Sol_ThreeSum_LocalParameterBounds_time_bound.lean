-- Prove2me | solution 1 for ThreeSum.LocalParameterBounds.time_bound
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-10-14T15:23:31.636856+00:00
-- url     : https://prove2.me/submissions/cf2fbdd8-1eda-4ce9-aa8d-4dd26cbe7b59

import Definitions.Def_APSPSource_RemainingDefinitions
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Logic
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Regions
import Definitions.Def_ThreeSum1962Source_Bundle01
import Definitions.Def_ThreeSum1962Source_Bundle02
import Definitions.Def_ThreeSum1962Source_Bundle03
import Definitions.Def_ThreeSum1962Source_Bundle04
import Definitions.Def_ThreeSum1962Source_Bundle06
import Definitions.Def_ThreeSum1962Source_Bundle07
import Definitions.Def_ThreeSum1962Source_Bundle10
import Definitions.Def_ThreeSum1962Source_Bundle11
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
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Floor.Div
import Mathlib.Algebra.Order.Group.Abs
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Algebra.Order.Group.Nat
import Mathlib.Algebra.Order.Group.Unbundled.Abs
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.NthRootLemmas
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Combinatorics.Colex
import Mathlib.Data.Fin.Embedding
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Range
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Int.Cast.Lemmas
import Mathlib.Data.Int.ModEq
import Mathlib.Data.Int.Notation
import Mathlib.Data.Int.SuccPred
import Mathlib.Data.List.Basic
import Mathlib.Data.List.GetD
import Mathlib.Data.List.MinMax
import Mathlib.Data.List.Nodup
import Mathlib.Data.Nat.Cast.Order.Ring
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
import Mathlib.Tactic.Abel
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Theorems.Thm_ThreeSum_LightSelectedPrime_time_bound


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
namespace Light
end Light
namespace ThreeSum.LightPascal
end ThreeSum.LightPascal
namespace ThreeSum.LightSubsetAddress
end ThreeSum.LightSubsetAddress
namespace ThreeSum.LocalCoverBounds
end ThreeSum.LocalCoverBounds
namespace ThreeSum.SubsetAddress
end ThreeSum.SubsetAddress

section


/-!
# A rectangular Pascal table in the benchmark language

Every coefficient is built once by addition from the preceding row.
The row-major representation supports one multiplication and two additions
per later lookup. No recursive binomial-coefficient evaluation is used.
-/

namespace ThreeSum.LightPascal

open Light

variable {lim : Limits} {P : Program} {d : ℕ}






















































































































































theorem buildTime_bound (L : ℕ) : buildTime L ≤ 1000*(L+1)^2 := by
  unfold buildTime rowTime LightArray.linearTime
  simp only [fillTime]
  nlinarith

end ThreeSum.LightPascal

end

section


/-!
# A complete subset-rank program, including table construction

This fixed program constructs both lookup tables in scratch and then ranks
one valid mask. Its cost is quadratic in the bit width. The faster cached
rank contract remains available separately, but no supplied table correctness
assumption appears in the fixed-program result below.
-/

namespace ThreeSum.LightSubsetSetup

open Light ThreeSum.SubsetAddress ThreeSum.LightPascal ThreeSum.LightSubsetAddress

variable {lim : Limits} {P : Program}
















































































theorem time_bound (L : ℕ) : time L ≤ 1200*(L+1)^2 := by
  have hb := buildTime_bound L
  unfold time powTableTime rankTime
  nlinarith

end ThreeSum.LightSubsetSetup

end

section


/-!
# Executing the local graph counts

One constructed Pascal table and one constructed power table provide all
integer counts needed by the local hash cover. The zero-mask rank call in
the reused setup wrapper takes only linear additional time. In particular,
none of these counts is an input oracle.
-/

namespace ThreeSum.LightLocalCounts

set_option maxHeartbeats 1000000
set_option maxRecDepth 4000

open Light LocalCoverBounds LightPascal LightSubsetAddress






































variable {lim : Limits} {P : Program} {d : ℕ}








































































































































theorem time_bound (h : ℕ) : time h ≤ 1700*(512*h+1)^2 := by
  have ht := LightSubsetSetup.time_bound (512*h)
  have hs : 0 < (512*h+1)^2 := Nat.pow_pos (by omega)
  unfold time
  nlinarith

end ThreeSum.LightLocalCounts

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

theorem width_bound (h : ℕ) : 512*h+1 ≤ 2^(h+10) := by
  have hh : h < 2^h := Nat.lt_two_pow_self
  have hp := pow_pos h
  rw [pow_add]
  norm_num
  omega

theorem count_time_bound (h : ℕ) : LightLocalCounts.time h ≤ 2^(2*h+31) := by
  calc
    LightLocalCounts.time h ≤ 1700*(512*h+1)^2 := LightLocalCounts.time_bound h
    _ ≤ 2^11*(2^(h+10))^2 := Nat.mul_le_mul (by decide) (Nat.pow_le_pow_left (width_bound h) 2)
    _ = 2^(2*h+31) := by rw [← pow_mul,← pow_add]; congr 1 <;> omega

theorem selected_time_bound (h : ℕ) :
    LightSelectedPrime.time (localThreshold h) ≤ 2^(1542*h+19) := by
  have ht := threshold_bound h
  have hx := pow_pos (514*h)
  have ha : localThreshold h+2 ≤ 2^(514*h+2) := by
    rw [pow_add]
    norm_num
    omega
  calc
    _ ≤ 6000*(localThreshold h+2)^3 := LightSelectedPrime.time_bound _
    _ ≤ 2^13*(2^(514*h+2))^3 := Nat.mul_le_mul (by decide) (Nat.pow_le_pow_left ha 3)
    _ = 2^(1542*h+19) := by rw [← pow_mul,← pow_add]; congr 1 <;> omega

theorem cap_time_bound (h : ℕ) :
    LightSmallDivide.time (LightLocalParameters.numerator h) (localPrime h) ≤ 2^(514*h+10) := by
  have hp := prime_bound h
  have hv := vertex_bound h
  have hx := pow_pos (514*h)
  rw [pow_add] at hp
  norm_num at hp
  have hn : LightLocalParameters.numerator h ≤ 24*2^(514*h) := by
    unfold LightLocalParameters.numerator
    omega
  have hq := Nat.div_le_self (LightLocalParameters.numerator h) (localPrime h)
  unfold LightSmallDivide.time
  rw [pow_add]
  norm_num
  omega

theorem time_bound_sourceProof (h : ℕ) : LightLocalParameters.time h ≤ envelope h := by
  have hc : LightLocalCounts.time h ≤ base h :=
    (count_time_bound h).trans (Nat.pow_le_pow_right (by decide) (by omega))
  have hp : LightSelectedPrime.time (localThreshold h) ≤ base h :=
    (selected_time_bound h).trans (Nat.pow_le_pow_right (by decide) (by omega))
  have hd : LightSmallDivide.time (LightLocalParameters.numerator h) (localPrime h) ≤ base h :=
    (cap_time_bound h).trans (Nat.pow_le_pow_right (by decide) (by omega))
  have hk : 200 ≤ base h := (by decide : 200 ≤ 2^8).trans
    (Nat.pow_le_pow_right (by decide) (by omega))
  have he : envelope h = 4*base h := by unfold envelope base; rw [pow_add]; norm_num; omega
  unfold LightLocalParameters.time
  rw [he]
  omega

































































































end ThreeSum.LocalParameterBounds

end


theorem solution : ∀ (h : Nat), @LE.le.{0} Nat instLENat (ThreeSum.LightLocalParameters.time h) (ThreeSum.LocalParameterBounds.envelope h) := by
  exact @ThreeSum.LocalParameterBounds.time_bound_sourceProof

#print axioms solution
