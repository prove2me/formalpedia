-- Prove2me | solution 1 for ThreeSum.SharedTraversalCosts.prefix_time_le
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-10-14T15:01:03.760373+00:00
-- url     : https://prove2.me/submissions/9129e3dd-05fd-4db5-aa9b-eefc25ddb02b

import Aesop
import Definitions.Def_APSPSource_RemainingDefinitions
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Logic
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Regions
import Definitions.Def_ThreeSum1962Source_Bundle01
import Definitions.Def_ThreeSum1962Source_Bundle04
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
import Mathlib.Algebra.Order.Ring.Nat
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
import Mathlib.Data.List.ProdSigma
import Mathlib.Data.List.Range
import Mathlib.Data.List.Sublists
import Mathlib.Data.List.TakeDrop
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

section


/-!
# Summing the actual dense-guard branches in physical slot order

The counter at slot i is the mass of slots before i. The expensive branch
is charged only when adding the current mass still fits the threshold.
These charges sum to at most that threshold, including when a later slot
crosses it. No bound on the mass of the crossing slot is required.
-/

namespace ThreeSum.SharedTraversalCosts

open Finset
open scoped BigOperators












theorem guardedMass_le_prefix (mass : ℕ → ℕ) (threshold n : ℕ) :
    guardedMass mass threshold n ≤ prefixMass mass n := by
  unfold guardedMass prefixMass
  exact sum_le_sum (fun i _ => by split <;> omega)

theorem guardedMass_le_threshold (mass : ℕ → ℕ) (threshold n : ℕ) :
    guardedMass mass threshold n ≤ threshold := by
  induction n with
  | zero => simp [guardedMass]
  | succ n ih =>
      have hp := guardedMass_le_prefix mass threshold n
      simp only [guardedMass,sum_range_succ] at ih ⊢
      by_cases hg : threshold < prefixMass mass n+mass n
      · simp only [if_pos hg,add_zero]
        exact ih
      · simp only [if_neg hg]
        change guardedMass mass threshold n+mass n ≤ threshold
        omega





theorem guardedBudget_eq (mass : ℕ → ℕ) (threshold initial work n : ℕ) :
    guardedBudget mass threshold initial work n =
      n*initial+guardedMass mass threshold n*work := by
  unfold guardedBudget guardedMass
  rw [sum_add_distrib,sum_mul]
  simp only [sum_const,card_range,smul_eq_mul]
  congr 1
  apply sum_congr rfl
  intro i hi
  split <;> simp

theorem guardedBudget_le (mass : ℕ → ℕ) (threshold initial work n : ℕ) :
    guardedBudget mass threshold initial work n ≤ n*initial+threshold*work := by
  rw [guardedBudget_eq]
  exact Nat.add_le_add_left (Nat.mul_le_mul_right work
    (guardedMass_le_threshold mass threshold n)) _

/-- A direct interface for the recursive ascending-slot machine counter. -/
theorem prefix_time_le_sourceProof {time mass : ℕ → ℕ} {threshold initial work : ℕ}
    (hzero : time 0 ≤ 30)
    (hstep : ∀ i, time (i+1) ≤ time i+initial+
      if threshold < prefixMass mass i+mass i then 0 else mass i*work) (n : ℕ) :
    time n ≤ 30+n*initial+threshold*work := by
  have hsum : ∀ n, time n ≤ 30+guardedBudget mass threshold initial work n := by
    intro k
    induction k with
    | zero => simpa [guardedBudget] using hzero
    | succ k ih =>
        have hs := hstep k
        simp only [guardedBudget,sum_range_succ] at ih ⊢
        omega
  have hh := guardedBudget_le mass threshold initial work n
  have hs := hsum n
  omega

end ThreeSum.SharedTraversalCosts

end


theorem solution : ∀ {time mass : Nat → Nat} {threshold initial work : Nat},
  @LE.le.{0} Nat instLENat (time (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@OfNat.ofNat.{0} Nat (nat_lit 30) (instOfNatNat (nat_lit 30))) →
    (∀ (i : Nat),
        @LE.le.{0} Nat instLENat
          (time
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) i
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) (time i) initial)
            (@ite.{1} Nat
              (@LT.lt.{0} Nat instLTNat threshold
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                  (ThreeSum.SharedTraversalCosts.prefixMass mass i) (mass i)))
              (threshold.decLt
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                  (ThreeSum.SharedTraversalCosts.prefixMass mass i) (mass i)))
              (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) (mass i) work)))) →
      ∀ (n : Nat),
        @LE.le.{0} Nat instLENat (time n)
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
              (@OfNat.ofNat.{0} Nat (nat_lit 30) (instOfNatNat (nat_lit 30)))
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) n initial))
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) threshold work)) := by
  exact @ThreeSum.SharedTraversalCosts.prefix_time_le_sourceProof

#print axioms solution
