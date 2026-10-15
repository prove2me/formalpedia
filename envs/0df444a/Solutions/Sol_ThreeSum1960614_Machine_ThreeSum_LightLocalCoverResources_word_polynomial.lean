-- Prove2me | solution 1 for ThreeSum1960614.Machine.ThreeSum.LightLocalCoverResources.word_polynomial
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-15T09:05:36.101403+00:00
-- url     : https://prove2.me/submissions/7eee966a-2597-40de-8dba-4a4faf25344a

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
import Mathlib.Algebra.Ring.Nat
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
import Mathlib.Data.Bool.Basic
import Mathlib.Data.Fin.Embedding
import Mathlib.Data.Fin.VecNotation
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
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Int.ModEq
import Mathlib.Data.Int.Notation
import Mathlib.Data.Int.SuccPred
import Mathlib.Data.List.Basic
import Mathlib.Data.List.GetD
import Mathlib.Data.List.MinMax
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.OfFn
import Mathlib.Data.List.Pi
import Mathlib.Data.List.Range
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
import Mathlib.Tactic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
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

local instance platformRadixNonzero_81d2cfbac6 (n : ℕ) : NeZero (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.radix n) :=
  ⟨Nat.ne_of_gt (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.radix_pos n)⟩


namespace Light
end Light
namespace ThreeSum
end ThreeSum
namespace ThreeSum.LightLocalCoverMagnitude
end ThreeSum.LightLocalCoverMagnitude
namespace ThreeSum.LightLocalCoverResources
end ThreeSum.LightLocalCoverResources
namespace ThreeSum.LocalCoverBounds
end ThreeSum.LocalCoverBounds
namespace ThreeSum1960614.Machine.Light
end ThreeSum1960614.Machine.Light
namespace ThreeSum1960614.Machine.ThreeSum
end ThreeSum1960614.Machine.ThreeSum
namespace ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
end ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
namespace ThreeSum1960614.Machine.ThreeSum.LightLocalCoverLayout
end ThreeSum1960614.Machine.ThreeSum.LightLocalCoverLayout
namespace ThreeSum1960614.Machine.ThreeSum.LightLocalCoverMagnitude
end ThreeSum1960614.Machine.ThreeSum.LightLocalCoverMagnitude
namespace ThreeSum1960614.Machine.ThreeSum.LightLocalCoverResources
end ThreeSum1960614.Machine.ThreeSum.LightLocalCoverResources
namespace ThreeSum1960614.Machine.ThreeSum.LightLocalCoverSchedule
end ThreeSum1960614.Machine.ThreeSum.LightLocalCoverSchedule
namespace ThreeSum1960614.Machine.ThreeSum.LightLocalCoverTables
end ThreeSum1960614.Machine.ThreeSum.LightLocalCoverTables
namespace ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
end ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds

section
open _root_.ThreeSum
open _root_.ThreeSum1960614.Machine.ThreeSum

open _root_.ThreeSum.LightLocalCoverResources
open _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverResources

open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.LocalCoverBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
open _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverSchedule
open _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverTables
open _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverLayout
open _root_.ThreeSum.LightLocalCoverMagnitude
open _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverMagnitude
set_option maxHeartbeats 1800000
section

theorem ThreeSum1960614.Machine.ThreeSum.LightLocalCoverResources.word_polynomial__implementation_5a80e76929 {h B : ℕ} (H : _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverMagnitude.Bounds h B) :
    _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverSetup.word h ≤ 2000*B^2 := by
  have hB := H.positive
  have hL := H.width
  have hn := H.vertices
  have hp := H.prime
  have hcap := H.cap
  have hN := H.candidates
  have hT := H.rounds
  have hP := H.decodePower
  have hmask := H.maskPower
  have hB2 : B ≤ B^2 := Nat.le_self_pow (by decide) B
  have hB2' : 1 ≤ B^2 := Nat.pow_pos (by omega)
  have hn2 : _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverLayout.vertices h*_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverLayout.vertices h ≤ B^2 := by
    have hh := Nat.pow_le_pow_left hn 2
    nlinarith
  have hp2 : _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime h*_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime h ≤ B^2 := by
    have hh := Nat.pow_le_pow_left hp 2
    nlinarith
  have hLp : (464*h+1)*_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime h ≤ B^2 := by
    calc
      _ ≤ B*B := Nat.mul_le_mul hL (by omega)
      _ = _ := by ring
  have hdecode : _root_.ThreeSum.LightWeightDecode.word (464*h) (_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime h) (_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverSchedule.rows h) ≤ 20*B := by
    unfold _root_.ThreeSum.LightWeightDecode.word _root_.ThreeSum.LightWeightRow.word
    omega
  have hhash : _root_.ThreeSum.LightHashHistogram.word (464*h) (_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime h) (_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime h) ≤ 22*B^2 := by
    unfold _root_.ThreeSum.LightHashHistogram.word _root_.ThreeSum.LightOneHot.word
    ring_nf at hLp hmask ⊢
    omega
  have hpair : _root_.ThreeSum.LightPairFlags.word (464*h) (_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverLayout.vertices h) (_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime h) (_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localBucketCap h) ≤ 700*B^2 := by
    unfold _root_.ThreeSum.LightPairFlags.word
    omega
  have hcandidate : _root_.ThreeSum.LightLocalCoverCandidate.word (464*h) (_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverLayout.vertices h)
      (_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime h) (_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localBucketCap h) (_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverSchedule.rows h) ≤ 742*B^2 := by
    unfold _root_.ThreeSum.LightLocalCoverCandidate.word
    omega
  have hgather : _root_.ThreeSum.LightWeightGather.word (_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverSchedule.rows h) (_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.scheduleSize h) (2*(464*h)) ≤ 5*B := by
    unfold _root_.ThreeSum.LightWeightGather.word
    omega
  have hhost : _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverHost.word h ≤ 747*B^2 := by
    unfold _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverHost.word
    change _root_.ThreeSum.LightLocalCoverCandidate.word (464*h) (_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverLayout.vertices h)
      (_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime h) (_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localBucketCap h) (_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverSchedule.rows h)+
      _root_.ThreeSum.LightWeightGather.word (_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverSchedule.rows h) (_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.scheduleSize h) (2*(464*h)) ≤ _
    omega
  have hbuild : _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverBuild.word h ≤ 748*B^2 := by
    unfold _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverBuild.word
    omega
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverSetup.word _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverSchedule.cols
  omega
end

end

theorem solution : type_of% (@ThreeSum1960614.Machine.ThreeSum.LightLocalCoverResources.word_polynomial__implementation_5a80e76929) := (@ThreeSum1960614.Machine.ThreeSum.LightLocalCoverResources.word_polynomial__implementation_5a80e76929)

#print axioms solution
