-- Prove2me | solution 1 for ThreeSum.SharedReportingBankResourceBounds.scaled_extent_le
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-10-14T15:41:33.152913+00:00
-- url     : https://prove2.me/submissions/04510695-1674-4bfd-96af-06a6d0896114

import Aesop
import Definitions.Def_APSPSource_RemainingDefinitions
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Logic
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Regions
import Definitions.Def_ThreeSum1962Source_Bundle01
import Definitions.Def_ThreeSum1962Source_Bundle14
import Definitions.Def_ThreeSum1962Source_Bundle15
import Definitions.Def_ThreeSum1962Source_Bundle16
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
import Theorems.Thm_ThreeSum_SharedReportingBankResourceBounds_components


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
namespace Light
end Light
namespace ThreeSum.Scales
end ThreeSum.Scales
namespace ThreeSum.SharedReportingBankHeader
end ThreeSum.SharedReportingBankHeader
namespace ThreeSum.SharedReportingBankLayout
end ThreeSum.SharedReportingBankLayout
namespace ThreeSum.SubsetAddress
end ThreeSum.SubsetAddress

section


/-! # Finite scale bounds for every shared-bank resource component -/

namespace ThreeSum.SharedReportingBankResourceBounds

open Scales Light SubsetAddress SharedReportingBankLayout SharedReportingBankHeader

set_option maxHeartbeats 3000000
set_option maxRecDepth 14000































































































theorem prefix_storage_le_magnitude (n : ℕ) :
    prefixStorage (half n) (blocks n) ≤ (magnitude n+1)^2 := by
  have H := components n
  have hmul := Nat.mul_le_mul (H.levelsBound.trans (Nat.le_succ _)) (Nat.add_le_add_right H.prefixBound 1)
  simpa only [prefixStorage,pow_two] using hmul












































theorem cell_le_magnitude (n : ℕ) : cellBound (half n) (blocks n) ≤ 20*(magnitude n+1)^3 := by
  have H := components n
  have hM := H.positive
  have hL := H.localWidthBound
  have hW := H.widthBound
  have hN := H.prefixBound
  have hE := H.pairsPower
  have hS := prefix_storage_le_magnitude n
  have hlocal : 2^(512*half n) ≤ magnitude n :=
    (Nat.pow_le_pow_right (by decide) (by omega)).trans H.localPower
  have hpower : 2^(width (half n) (blocks n)) ≤ magnitude n :=
    (Nat.pow_le_pow_right (by decide) (by omega)).trans H.widthPower
  have hquad := Nat.pow_le_pow_left hW 2
  have hbox := Nat.mul_le_mul (Nat.mul_le_mul hN hW) hpower
  unfold cellBound
  nlinarith

theorem scaled_extent_le_sourceProof (n : ℕ) : scaledExtent n ≤ polynomialPart n := by
  have H := components n
  have hK : levels (blocks n) ≤ magnitude n+1 := by have hh := H.levelsBound; omega
  have hc := cell_le_magnitude n
  have hp4 : magnitude n+1 ≤ (magnitude n+1)^4 := Nat.le_self_pow (by decide) _
  have hlevels := Nat.mul_le_mul hK hc
  have hterm : 5*levels (blocks n)+levels (blocks n)*cellBound (half n) (blocks n) ≤
      25*(magnitude n+1)^4 := by nlinarith
  have hrows := Nat.mul_le_mul (H.occurrence.trans (Nat.le_succ _))
    (show n*n ≤ (n+1)^2 by nlinarith)
  have hprod : LightBlockSourceCatalog.count (half n) (blocks n)*n*n*
      (5*levels (blocks n)+levels (blocks n)*cellBound (half n) (blocks n)) ≤
      25*(magnitude n+1)^5*(n+1)^2 := by
    have hh := Nat.mul_le_mul hrows hterm
    nlinarith only [hh]
  have hquad : (512*half n+1)^2 ≤ (magnitude n+1)^5 := by
    simpa only [Nat.succ_eq_add_one] using
      (Nat.pow_le_pow_left (H.localWidthBound.trans (Nat.le_succ _)) 2).trans
        (Nat.pow_le_pow_right (by omega) (by decide : 2 ≤ 5))
  have hp : 1 ≤ (magnitude n+1)^5 := Nat.one_le_pow _ _ (by omega)
  have hinit : 9+(512*half n+1)^2 ≤ 10*(magnitude n+1)^5 := by omega
  have hn : 1 ≤ (n+1)^2 := Nat.one_le_pow _ _ (by omega)
  have hinit' := hinit.trans (Nat.le_mul_of_pos_right _ hn)
  unfold scaledExtent extent polynomialPart
  calc
    _ ≤ 10*(magnitude n+1)^5*(n+1)^2+25*(magnitude n+1)^5*(n+1)^2 :=
      Nat.add_le_add hinit' hprod
    _ = 35*(magnitude n+1)^5*(n+1)^2 := by ring
    _ ≤ _ := Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (by decide : 35 ≤ 5000))


























































































end ThreeSum.SharedReportingBankResourceBounds

end


theorem solution : ∀ (n : Nat),
  @LE.le.{0} Nat instLENat (ThreeSum.SharedReportingBankResourceBounds.scaledExtent n)
    (ThreeSum.SharedReportingBankResourceBounds.polynomialPart n) := by
  exact @ThreeSum.SharedReportingBankResourceBounds.scaled_extent_le_sourceProof

#print axioms solution
