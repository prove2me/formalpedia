-- Prove2me | solution 1 for ThreeSum.LightLocalCoverResources.space_polynomial
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-10-14T14:45:09.218832+00:00
-- url     : https://prove2.me/submissions/e2aead84-8e23-4258-afbc-8d8707412528

import Aesop
import Definitions.Def_APSPSource_RemainingDefinitions
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Logic
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Regions
import Definitions.Def_ThreeSum1962Source_Bundle01
import Definitions.Def_ThreeSum1962Source_Bundle07
import Definitions.Def_ThreeSum1962Source_Bundle10
import Definitions.Def_ThreeSum1962Source_Bundle11
import Definitions.Def_ThreeSum1962Source_Bundle12
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
import Mathlib.Data.Finset.Card
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
import Mathlib.Data.List.Range
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
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.Tauto


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
namespace Light
end Light
namespace ThreeSum.GlobalEncoding
end ThreeSum.GlobalEncoding
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

section


/-! # A packed layout for the complete local-cover constructor -/

namespace ThreeSum.LightLocalCoverLayout

open Light LocalCoverBounds GlobalEncoding LightLocalCoverSchedule LightLocalCoverTables


















theorem space_shift (base h : ℕ) : space base h = base+space 0 h := by
  unfold space scheduleMaps work matrixPtr hist1 hist0 raw1 raw0 maps bitPtr LightLocalCoverCandidate.space
  omega





























end ThreeSum.LightLocalCoverLayout

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







































































theorem space_polynomial_sourceProof {h B : ℕ} (H : Bounds h B) (base : ℕ) :
    space base h ≤ base+20*B^3 := by
  have hB := H.positive
  have hL := H.width
  have hn := H.vertices
  have hp := H.prime
  have hN := H.candidates
  have hT := H.rounds
  have hB13 : B ≤ B^3 := Nat.le_self_pow (by decide) B
  have hB12 : B ≤ B^2 := Nat.le_self_pow (by decide) B
  have hB23 := Nat.pow_le_pow_right hB (by decide : 2 ≤ 3)
  have hB2 : 1 ≤ B^2 := Nat.pow_pos (by omega)
  have hvL : vertices h*(512*h) ≤ B^2 := by
    calc
      _ ≤ B*B := Nat.mul_le_mul (by omega) (by omega)
      _ = _ := by ring
  have hNL : rows h*(2*(512*h)) ≤ 2*B^2 := by
    calc
      _ ≤ B*(2*B) := Nat.mul_le_mul (by omega) (by omega)
      _ = _ := by ring
  have hNp : rows h*localPrime h ≤ B^2 := by
    calc
      _ ≤ B*B := Nat.mul_le_mul (by omega) (by omega)
      _ = _ := by ring
  have hp2 : cols h ≤ B^2 := by
    have hh := Nat.pow_le_pow_left hp 2
    unfold cols
    nlinarith
  have hn2 : vertices h*vertices h ≤ B^2 := by
    have hh := Nat.pow_le_pow_left hn 2
    nlinarith
  have hNp2 : rows h*cols h ≤ B^3 := by
    calc
      _ ≤ B*(B^2) := Nat.mul_le_mul (by omega) hp2
      _ = _ := by ring
  have hT2L : scheduleSize h*(2*(512*h)) ≤ 2*B^2 := by
    calc
      _ ≤ B*(2*B) := Nat.mul_le_mul (by omega) (by omega)
      _ = _ := by ring
  have hwork : work 0 h ≤ 11*B^3 := by
    unfold work matrixPtr hist1 hist0 raw1 raw0 maps bitPtr
    omega
  have hLp : 512*h*localPrime h ≤ B^2 := by
    calc
      _ ≤ B*B := Nat.mul_le_mul (by omega) (by omega)
      _ = _ := by ring
  have hlog := Nat.log_le_self 2 (512*h*localPrime h+1)
  have hmax : max (512*h+1) (Nat.log 2 (512*h*localPrime h+1)+2) ≤ 4*B^2 := by omega
  have hscratch : LightLocalCoverCandidate.space (work 0 h) (512*h) (vertices h) (localPrime h) ≤ 20*B^3 := by
    unfold LightLocalCoverCandidate.space
    omega
  have hout : scheduleMaps 0 h+scheduleSize h*(2*(512*h)) ≤ 20*B^3 := by
    unfold scheduleMaps LightCoverGreedy.total
    omega
  rw [space_shift]
  exact Nat.add_le_add_left (max_le hscratch hout) base














































































end ThreeSum.LightLocalCoverResources

end


theorem solution : ∀ {h B : Nat},
  ThreeSum.LightLocalCoverMagnitude.Bounds h B →
    ∀ (base : Nat),
      @LE.le.{0} Nat instLENat (ThreeSum.LightLocalCoverLayout.space base h)
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) base
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
            (@OfNat.ofNat.{0} Nat (nat_lit 20) (instOfNatNat (nat_lit 20)))
            (@HPow.hPow.{0, 0, 0} Nat Nat Nat
              (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid))) B
              (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))) := by
  exact @ThreeSum.LightLocalCoverResources.space_polynomial_sourceProof

#print axioms solution
