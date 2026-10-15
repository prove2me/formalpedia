-- Prove2me | solution 1 for ThreeSum.SharedTraversalCosts.prefix_time_le_dispatch_budget
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-10-14T15:30:50.939393+00:00
-- url     : https://prove2.me/submissions/d1d6b357-4ede-47e1-99f8-0cd2d01c3889

import Aesop
import Definitions.Def_APSPSource_RemainingDefinitions
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Logic
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Regions
import Definitions.Def_ThreeSum1962Source_Bundle01
import Definitions.Def_ThreeSum1962Source_Bundle02
import Definitions.Def_ThreeSum1962Source_Bundle04
import Definitions.Def_ThreeSum1962Source_Bundle08
import Definitions.Def_ThreeSum1962Source_Bundle09
import Definitions.Def_ThreeSum1962Source_Bundle10
import Definitions.Def_ThreeSum1962Source_Bundle11
import Definitions.Def_ThreeSum1962Source_Bundle15
import Definitions.Def_TrulySubcubicAPSP_SourceSpecification
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
import Mathlib.Analysis.SpecialFunctions.Log.Basic
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
import Mathlib.Data.Int.Cast.Lemmas
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
import Mathlib.Data.Nat.Cast.Order.Ring
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
import Theorems.Thm_ThreeSum_SharedReportingBankLevels_candidates_nonempty
import Theorems.Thm_ThreeSum_SharedTraversalCosts_prefix_time_le


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
namespace ThreeSum.CostLedger
end ThreeSum.CostLedger
namespace ThreeSum.LightBlockQuery
end ThreeSum.LightBlockQuery
namespace ThreeSum.LocalCoverBounds
end ThreeSum.LocalCoverBounds
namespace ThreeSum.Parameters
end ThreeSum.Parameters
namespace ThreeSum.ReportingHostLevelData
end ThreeSum.ReportingHostLevelData
namespace ThreeSum.Scales
end ThreeSum.Scales
namespace ThreeSum.StageBounds
end ThreeSum.StageBounds

section


/-!
# The executable integer cubic switch

The implementation scans integers `q ≤ r/2` and tests a cleared integer
inequality.  No real-number comparison, logarithm oracle, or unbounded
noncomputable search occurs in the definition.  For admissible depths the
candidate set is nonempty.  Minimality gives the exact `9/r` rounding error
needed by the certified box and entropy bounds.
-/

namespace ThreeSum.Switch

open Set ThreeSum.Parameters ThreeSum.Scales

set_option maxHeartbeats 0






















@[simp] theorem mem_candidates {J j r q : ℕ} :
    q ∈ candidates J j r ↔ q ≤ r / 2 ∧ accepts J j r q := by
  simp [candidates, Nat.lt_succ_iff]

theorem switchIndex_mem {J j r : ℕ} (h : (candidates J j r).Nonempty) :
    switchIndex J j r ∈ candidates J j r := by
  simp only [switchIndex, dif_pos h]
  exact Finset.min'_mem _ _







noncomputable section









































































































































































































end
end ThreeSum.Switch

end

section


/-!
# The physical reporting catalogs use the certified traversal ledger

The switch in every retained catalog is the literal switch used by the
original finite ledger. This module connects the executed level and terminal
costs to those exact binomial terms, preserving the sum over levels.
-/

namespace ThreeSum.SharedTraversalCosts

open Finset Scales LocalCoverBounds LightBlockQuery ReportingHostLevelData
open StageBounds CostLedger
open scoped BigOperators

set_option maxHeartbeats 2400000
set_option maxRecDepth 12000





theorem residual_eq (n k : ℕ) :
    residualSize (half n) (blocks n) k=Switch.residualSize n k := rfl











theorem switch_le_half {n k : ℕ} (hk : k ≤ Switch.terminalDepth n) :
    Switch.actualSwitch n k ≤ Switch.residualSize n k/2 := by
  have hn := SharedReportingBankLevels.candidates_nonempty
    (h := half n) (J := blocks n) (k := k) hk
  have hm := (Switch.mem_candidates.mp (Switch.switchIndex_mem hn)).1
  have hr : SharedReportingBankLevels.residual (half n) (blocks n) k=Switch.residualSize n k := by
    rw [← residual_eq]
    unfold SharedReportingBankLevels.residual residualSize
    ring
  rw [hr] at hm
  exact hm

theorem query_terms_pos {n k : ℕ} (hk : k ≤ Switch.terminalDepth n) : 0 < queryTerms n k :=
  Nat.choose_pos ((switch_le_half hk).trans (Nat.div_le_self _ _))

































































































open Filter Real Parameters
open scoped Topology

noncomputable section












































end
end ThreeSum.SharedTraversalCosts

end

section


/-!
# Include the executed wanted decoder and scratch-pointer constructor

The actual physical indices have a size-only bound, independently of the
input integer magnitude. Their logarithmic decoder cost and the literal
layout power loop therefore contribute exponent zero. A fixed caller cost
is included explicitly for the remaining register loads and calls.
-/

namespace ThreeSum.SharedTraversalCosts

open Scales StageBounds CostLedger LightBlockQuery

set_option maxHeartbeats 2000000
set_option maxRecDepth 12000







































theorem prefix_time_le_dispatch_budget_sourceProof {time mass : ℕ → ℕ} {c n k threshold count : ℕ}
    (hzero : time 0 ≤ 30)
    (hstep : ∀ i, time (i+1) ≤ time i+(scaledOverhead n*queryTerms n 0+scalarOverhead c n)+
      if threshold < prefixMass mass i+mass i then 0 else
        mass i*(scaledOverhead n*(microPartitions n*allQueryTerms n+terminalChoices n)))
    (hcount : count ≤ UniformStageBounds.wantedBudget n)
    (hthreshold : threshold ≤ UniformStageBounds.falseBudget k n*TrimScales.representationBound n) :
    time count ≤ dispatchBudget c k n := by
  have ht := prefix_time_le hzero hstep count
  have hq := Nat.le_mul_of_pos_right (scalarOverhead c n)
    (query_terms_pos (n := n) (k := 0) (by omega))
  have hinit : scaledOverhead n*queryTerms n 0+scalarOverhead c n ≤
      totalOverhead c n*queryTerms n 0 := by unfold totalOverhead; nlinarith only [hq]
  have hwork : scaledOverhead n*(microPartitions n*allQueryTerms n+terminalChoices n) ≤
      totalOverhead c n*(microPartitions n*allQueryTerms n+terminalChoices n) :=
    Nat.mul_le_mul_right _ (Nat.le_add_right _ _)
  have hi := Nat.mul_le_mul hcount hinit
  have ha := Nat.mul_le_mul hthreshold hwork
  have hs := ht.trans (Nat.add_le_add (Nat.add_le_add_left hi 30) ha)
  unfold dispatchBudget initialCount activeCount terminalCount
  calc
    time count ≤ (30+UniformStageBounds.wantedBudget n*(totalOverhead c n*queryTerms n 0)+
        UniformStageBounds.falseBudget k n*TrimScales.representationBound n*
          (totalOverhead c n*(microPartitions n*allQueryTerms n+terminalChoices n)))+
        totalOverhead c n*UniformStageBounds.falseBudget k n*TrimScales.representationBound n*terminalChoices n :=
      hs.trans (Nat.le_add_right _ _)
    _ = _ := by ring

open Filter Real Parameters
open scoped Topology

noncomputable section



































end
end ThreeSum.SharedTraversalCosts

end


theorem solution : ∀ {time mass : Nat → Nat} {c n k threshold count : Nat},
  @LE.le.{0} Nat instLENat (time (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@OfNat.ofNat.{0} Nat (nat_lit 30) (instOfNatNat (nat_lit 30))) →
    (∀ (i : Nat),
        @LE.le.{0} Nat instLENat
          (time
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) i
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) (time i)
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                  (ThreeSum.SharedTraversalCosts.scaledOverhead n)
                  (ThreeSum.CostLedger.queryTerms n (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
                (ThreeSum.SharedTraversalCosts.scalarOverhead c n)))
            (@ite.{1} Nat
              (@LT.lt.{0} Nat instLTNat threshold
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                  (ThreeSum.SharedTraversalCosts.prefixMass mass i) (mass i)))
              (threshold.decLt
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                  (ThreeSum.SharedTraversalCosts.prefixMass mass i) (mass i)))
              (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) (mass i)
                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                  (ThreeSum.SharedTraversalCosts.scaledOverhead n)
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                      (ThreeSum.CostLedger.microPartitions n) (ThreeSum.CostLedger.allQueryTerms n))
                    (ThreeSum.StageBounds.terminalChoices n))))))) →
      @LE.le.{0} Nat instLENat count (ThreeSum.UniformStageBounds.wantedBudget n) →
        @LE.le.{0} Nat instLENat threshold
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
              (ThreeSum.UniformStageBounds.falseBudget k n) (ThreeSum.TrimScales.representationBound n)) →
          @LE.le.{0} Nat instLENat (time count) (ThreeSum.SharedTraversalCosts.dispatchBudget c k n) := by
  exact @ThreeSum.SharedTraversalCosts.prefix_time_le_dispatch_budget_sourceProof

#print axioms solution
