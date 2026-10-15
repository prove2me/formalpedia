-- Prove2me | solution 1 for ThreeSum.BlockSourceCoverInput.Input.of_kept
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-10-14T14:41:22.123399+00:00
-- url     : https://prove2.me/submissions/a792e14e-75c8-4930-b05f-32383712fca3

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
import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Algebra.Ring.Nat
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
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Tactic
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
namespace ThreeSum.BlockCoefficientRows
end ThreeSum.BlockCoefficientRows
namespace ThreeSum.BlockSourceFlags
end ThreeSum.BlockSourceFlags
namespace ThreeSum.GlobalEncoding
end ThreeSum.GlobalEncoding
namespace ThreeSum.LocalCoverBounds
end ThreeSum.LocalCoverBounds

section


/-!
# Constructed local-cover output as source-encoding input

This adapter connects the actual cover builder's retained candidate tables
and gathered occurrence rows to the exact reads used by source preparation.
Occurrence order, repeated candidates, and both independent bucket tables
are preserved without further searching or histogram construction.
-/

namespace ThreeSum.BlockSourceCoverInput

open Light GlobalEncoding LocalCoverBounds BlockCoefficientRows BlockSourceFlags





























theorem Input.of_kept_sourceProof {μ ν : ℕ → ℤ} {h maps candidates histL histR bound : ℕ}
    (H : Input μ h maps candidates histL histR) (K : Kept μ ν bound)
    (hmaps : maps+2*(512*h)*scheduleSize h ≤ bound)
    (hcandidates : candidates+scheduleSize h ≤ bound)
    (hleft : histL+LightLocalCoverSchedule.rows h*localPrime h ≤ bound)
    (hright : histR+LightLocalCoverSchedule.rows h*localPrime h ≤ bound) :
    Input ν h maps candidates histL histR := by
  refine ⟨?_,?_,?_,?_,?_⟩
  · intro s
    rw [K _ (by have hs := s.isLt; omega)]
    exact H.candidates s
  · intro s hs t ht
    have he := Nat.mul_le_mul_left (2*(512*h)) (show s+1 ≤ scheduleSize h by omega)
    simp only [Nat.mul_add,Nat.mul_one] at he
    rw [K _ (by omega)]
    exact H.leftRows s hs t ht
  · intro s hs t ht
    have he := Nat.mul_le_mul_left (2*(512*h)) (show s+1 ≤ scheduleSize h by omega)
    simp only [Nat.mul_add,Nat.mul_one] at he
    rw [K _ (by omega)]
    exact H.rightRows s hs t ht
  · intro k hk r hr
    have he := Nat.mul_le_mul_right (localPrime h) (show k+1 ≤ LightLocalCoverSchedule.rows h by omega)
    simp only [Nat.add_mul,Nat.one_mul] at he
    rw [K _ (by omega)]
    exact H.leftCounts k hk r hr
  · intro k hk r hr
    have he := Nat.mul_le_mul_right (localPrime h) (show k+1 ≤ LightLocalCoverSchedule.rows h by omega)
    simp only [Nat.add_mul,Nat.one_mul] at he
    rw [K _ (by omega)]
    exact H.rightCounts k hk r hr

end ThreeSum.BlockSourceCoverInput

end


theorem solution : ∀ {μ ν : Nat → Int} {h maps candidates histL histR bound : Nat},
  ThreeSum.BlockSourceCoverInput.Input μ h maps candidates histL histR →
    Light.Kept μ ν bound →
      @LE.le.{0} Nat instLENat
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) maps
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                  (@OfNat.ofNat.{0} Nat (nat_lit 512) (instOfNatNat (nat_lit 512))) h))
              (ThreeSum.GlobalEncoding.scheduleSize h)))
          bound →
        @LE.le.{0} Nat instLENat
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) candidates
              (ThreeSum.GlobalEncoding.scheduleSize h))
            bound →
          @LE.le.{0} Nat instLENat
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) histL
                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                  (ThreeSum.LightLocalCoverSchedule.rows h) (ThreeSum.LocalCoverBounds.localPrime h)))
              bound →
            @LE.le.{0} Nat instLENat
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) histR
                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                    (ThreeSum.LightLocalCoverSchedule.rows h) (ThreeSum.LocalCoverBounds.localPrime h)))
                bound →
              ThreeSum.BlockSourceCoverInput.Input ν h maps candidates histL histR := by
  exact @ThreeSum.BlockSourceCoverInput.Input.of_kept_sourceProof

#print axioms solution
