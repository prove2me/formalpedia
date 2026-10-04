-- Prove2me | solution 1 for ProximityPrize.SubmissionLower.Lower80889.Budgets.joint_charge_yukon_b9dc1c835101
-- status  : ACCEPTED   (prove)
-- author  : @yukon
-- created : 2026-10-02T17:38:18.78806+00:00
-- url     : https://prove2.me/submissions/f4b9f130-ef41-47d2-91ec-94dfa49cf566

import Definitions.Def_Yukon_34c6baedbec234911ae26a26


import Definitions.Def_Yukon_0e3496485be9a551c983331b






import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.Data.Nat.Log
import Init.Data.Vector.OfFn
import Mathlib.Algebra.Order.Star.Basic
import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Tactic.Cases
import Mathlib.Order.Lattice.Nat
import Mathlib.Data.List.GetD
import Mathlib.Algebra.GroupWithZero.Nat
import Init
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.Algebra.Tropical.Basic
import Mathlib.Tactic.Linarith
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Algebra.Field.TransferInstance
import Mathlib.Tactic.Ring
import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Nat.ModEq
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.FieldSimp
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.NumberTheory.LucasPrimality
import Mathlib.Tactic.ReduceModChar
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.ENNReal.Inv
import Mathlib.Data.ENat.Basic
import Mathlib.Data.ENat.Defs
import Mathlib.Data.Nat.Cast.Order.Field
import Mathlib.Algebra.CharP.Defs
import Mathlib.Data.NNReal.Basic
import Mathlib.Data.NNReal.Defs
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finsupp.Basic
import Mathlib.Data.Nat.Digits.Defs
import Mathlib.Data.Nat.Bitwise
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.IntervalCases
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.Ring.Regular
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Data.Real.ENatENNReal
import Mathlib.Topology.MetricSpace.Infsep
import Mathlib.Tactic.Qify
import Mathlib.InformationTheory.Hamming
import Mathlib.Data.ENat.Lattice
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.RingTheory.Henselian
import Mathlib.LinearAlgebra.AffineSpace.Combination
import Mathlib.LinearAlgebra.AffineSpace.Pointwise
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Tactic.DepRewrite
import Mathlib.Data.Fin.Basic
import Batteries.Data.Fin.Fold
import Mathlib.Tactic.FinCases
import Mathlib.Data.Fin.Tuple.Take
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Order.Sub.Basic
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.PicardGroup
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.FieldTheory.Finiteness
import Mathlib.Analysis.Normed.Field.Lemmas
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.LinearAlgebra.StdBasis
import Mathlib.Order.CompletePartialOrder
import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.Algebra.BigOperators.Finsupp.Fin
import Mathlib.Data.Finsupp.Fin
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Data.FinEnum
import Mathlib.Algebra.Group.Action.Pointwise.Finset
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.SchwartzZippel
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Data.Rat.Star
import Mathlib.Probability.Notation
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.FieldTheory.RatFunc.AsPolynomial
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.RingTheory.Polynomial.Resultant.Basic
import Aesop
import Mathlib.Algebra.Polynomial.Bivariate
import Mathlib.Algebra.Ring.TransferInstance
import Mathlib.Algebra.Polynomial.Inductions
import Mathlib.Algebra.Polynomial.OfFn
import Mathlib.RingTheory.Polynomial.UniqueFactorization
import Mathlib.LinearAlgebra.Matrix.Determinant.Misc
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.Data.Matrix.Block
import Mathlib.Data.Matrix.Mul
import Mathlib.Algebra.Field.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finset.Insert
import Mathlib.Algebra.Polynomial.Degree.Defs
import Mathlib.Algebra.Polynomial.Basic
import Init.Data.List.FinRange
import Mathlib.Data.Matrix.Reflection
import Mathlib.Logic.Function.Basic
import Mathlib.Data.Fin.Tuple.Embedding
import Mathlib.Data.Nat.Find
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Algebra.GroupWithZero.Units.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Algebra.Polynomial.Degree.SmallDegree
import Mathlib.LinearAlgebra.Matrix.Polynomial
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Algebra.Polynomial.Degree.Units
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fin.SuccPred
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.LinearAlgebra.Matrix.RowCol
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Data.Finset.Preimage
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Fin
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Tactic.ComputeDegree
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Probability.ProbabilityMassFunction.Basic
import Batteries.Tactic.Lint
import Mathlib.Data.PFunctor.Multivariate.Basic
import Mathlib.Data.PFunctor.Univariate.Basic
import Mathlib.Tactic.Common
import Mathlib.Init
import Lean.Message
import Batteries.Tactic.Lint.Basic
import Mathlib.CategoryTheory.Monad.Types
import Mathlib.Order.CompleteLattice.Basic
import Batteries.Control.Lemmas
import Mathlib.Data.Vector.Defs
import Batteries.Control.OptionT
import Batteries.Control.AlternativeMonad
import Mathlib.Data.Fintype.Vector
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Perm
import Init.Data.UInt.Lemmas
import Mathlib.Logic.Embedding.Basic
import Mathlib.Data.List.Sym
import Mathlib.Order.Basic
import Mathlib.Control.Monad.Writer
import Mathlib.Algebra.Group.TypeTags.Basic
import Mathlib.Algebra.Group.Hom.Defs
import Mathlib.Algebra.Group.Pi.Basic
import Mathlib.Algebra.FreeMonoid.Basic
import Mathlib.Data.Set.Card
import Init.Data.Vector.Lemmas
import Mathlib.Control.Lawful
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Logic.Equiv.Sum
import Std.Tactic.Do
import Std.Internal.Do.Assertion
import Mathlib.Algebra.Order.Monoid.Defs
import Init.Data.String.Lemmas.Iterate
import Init.Data.String.Termination
import Init.Data.String.Lemmas.Splits
import Init.Data.String.Iterate
import Init.Data.String.Defs
import Init.Omega
import Init.Data.Slice.Lemmas
import Init.Data.Nat.Mod
import Init.Data.List.TakeDrop
import Init.Data.List.Range
import Init.Data.List.Nat.TakeDrop
import Init.Data.List.Nat.Range
import Init.Data.Iterators.Lemmas
import Init.Data.Range
import Init.Data.Iterators.Lemmas.Combinators.FilterMap
import Std.Do.Triple.SpecLemmas
import Init.Data.Slice.Array
import Init.Data.Range.Polymorphic
import Init.Data.Range.Polymorphic.Iterators
import Init.While
import Init.Syntax
import Lean.Meta.Sym.Pattern
import Lean.Meta.Tactic.Simp
import Lean.Meta.Match.MatcherApp
import Lean.Elab.Tactic.Basic
import Lean.Elab.Tactic.Do.Attr
import Lean.Meta.Sym.Simp.DiscrTree
import Lean.Meta.Sym.Util
import Lean.Meta.Sym.Simp.Rewrite
import Lean.Meta.Sym.Simp.Goal
import Lean.Meta.Tactic.TryThis
import Lean.Meta.Sym.Apply
import Mathlib.Analysis.Convex.Basic
import Mathlib.Topology.ContinuousMap.Basic
import Mathlib.Topology.Instances.Discrete
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Order.Fin.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Finsupp.Order
import Std.Data.HashMap.Lemmas
import Mathlib.Data.NNRat.BigOperators
import Mathlib.Data.DFinsupp.BigOperators
import Mathlib.Data.FunLike.Basic
import Mathlib.Data.PFunctor.Univariate.M
import Mathlib.Logic.Equiv.Prod
import Mathlib.Analysis.Asymptotics.SuperpolynomialDecay
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.Order.Lattice
import Mathlib.Order.BoundedOrder.Basic
import Mathlib.Logic.Equiv.Defs
import Mathlib.Logic.Relation
import Mathlib.Data.Fintype.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Data.Set.Basic
import Mathlib.Tactic.Use
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.Algebra.Order.Antidiag.Pi
import Mathlib.Data.Sym.Card
import Mathlib.Order.Interval.Finset.Fin
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.Attr.Register
import Batteries.Data.Vector.Lemmas
import Mathlib.Data.Vector.Basic
import Mathlib.NumberTheory.Zsqrtd.GaussianInt
import Mathlib.Algebra.EuclideanDomain.Int
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.RingTheory.UniqueFactorizationDomain.Defs
import Mathlib.RingTheory.AdjoinRoot
import Lean.Compiler.IR
import Mathlib.Topology.LocallyConstant.Basic
import Mathlib.Topology.JacobsonSpace
import Mathlib.RingTheory.ZMod
import Mathlib.RingTheory.Valuation.RankOne
import Mathlib.RingTheory.Valuation.Integral
import Mathlib.RingTheory.Valuation.Discrete.RankOne
import Mathlib.RingTheory.Valuation.Discrete.IsDiscreteValuationRing
import Mathlib.RingTheory.Unramified.Locus
import Mathlib.RingTheory.Unramified.LocalRing
import Mathlib.RingTheory.Unramified.Finite
import Mathlib.RingTheory.Unramified.Field
import Mathlib.RingTheory.Unramified.Basic
import Mathlib.RingTheory.UniqueFactorizationDomain.Multiplicative
import Mathlib.RingTheory.UniqueFactorizationDomain.Finsupp
import Mathlib.RingTheory.TensorProduct.Pi
import Mathlib.RingTheory.TensorProduct.IsBaseChangePi
import Mathlib.RingTheory.Spectrum.Prime.TensorProduct
import Mathlib.RingTheory.Spectrum.Prime.Jacobson
import Mathlib.RingTheory.Spectrum.Prime.FreeLocus
import Mathlib.RingTheory.RingHom.Finite
import Mathlib.RingTheory.RamificationInertia.Ramification
import Mathlib.RingTheory.RamificationInertia.Inertia
import Mathlib.RingTheory.RamificationInertia.Basic
import Mathlib.RingTheory.QuasiFinite.Basic
import Mathlib.RingTheory.Polynomial.ContentIdeal
import Mathlib.RingTheory.OrderOfVanishing.Basic
import Mathlib.RingTheory.NormalClosure
import Mathlib.RingTheory.Norm.Transitivity
import Mathlib.RingTheory.Norm.Basic
import Mathlib.RingTheory.Nilpotent.Exp
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
import Mathlib.RingTheory.MvPolynomial.MonomialOrder.DegLex
import Mathlib.RingTheory.MvPolynomial.MonomialOrder
import Mathlib.RingTheory.MvPolynomial.Localization
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.RingTheory.Localization.NormTrace
import Mathlib.RingTheory.Localization.InvSubmonoid
import Mathlib.RingTheory.Localization.Free
import Mathlib.RingTheory.LocalRing.ResidueField.Instances
import Mathlib.RingTheory.LocalRing.ResidueField.Fiber
import Mathlib.RingTheory.LocalRing.Length
import Mathlib.RingTheory.LocalProperties.Projective
import Mathlib.RingTheory.Jacobson.Artinian
import Mathlib.RingTheory.Invariant.Galois
import Mathlib.RingTheory.Invariant.Basic
import Mathlib.RingTheory.IntegralClosure.IntegralRestrict
import Mathlib.RingTheory.Int.Basic
import Mathlib.RingTheory.Ideal.Norm.RelNorm
import Mathlib.RingTheory.Ideal.Norm.AbsNorm
import Mathlib.RingTheory.Ideal.IsPrincipal
import Mathlib.RingTheory.Ideal.Int
import Mathlib.RingTheory.Ideal.Basis
import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Submodule
import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Ideal
import Mathlib.RingTheory.GradedAlgebra.Basic
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.Finiteness.Quotient
import Mathlib.RingTheory.Finiteness.NilpotentKer
import Mathlib.RingTheory.Etale.Kaehler
import Mathlib.RingTheory.Discriminant
import Mathlib.RingTheory.Derivation.ToSquareZero
import Mathlib.RingTheory.DedekindDomain.PID
import Mathlib.RingTheory.DedekindDomain.Instances
import Mathlib.RingTheory.DedekindDomain.Factorization
import Mathlib.RingTheory.Adjoin.Polynomial.Bivariate
import Mathlib.Order.GameAdd
import Mathlib.NumberTheory.RamificationInertia.Valuation
import Mathlib.NumberTheory.RamificationInertia.Ramification
import Mathlib.NumberTheory.RamificationInertia.Inertia
import Mathlib.NumberTheory.RamificationInertia.Galois
import Mathlib.NumberTheory.RamificationInertia.Basic
import Mathlib.NumberTheory.FunctionField
import Mathlib.LinearAlgebra.TensorProduct.Prod
import Mathlib.LinearAlgebra.Quotient.Pi
import Mathlib.LinearAlgebra.FreeModule.Finite.Quotient
import Mathlib.LinearAlgebra.FreeModule.Finite.CardQuotient
import Mathlib.LinearAlgebra.FreeModule.Determinant
import Mathlib.GroupTheory.Submonoid.Inverses
import Mathlib.FieldTheory.RatFunc.Valuation
import Mathlib.FieldTheory.RatFunc.IntermediateField
import Mathlib.FieldTheory.RatFunc.Degree
import Mathlib.FieldTheory.Galois.IsGaloisGroup
import Mathlib.Data.ZMod.QuotientRing
import Mathlib.Data.Real.Embedding
import Mathlib.Data.Int.NatAbs
import Mathlib.Data.Int.Associated
import Mathlib.Data.Finsupp.WellFounded
import Mathlib.Data.Finsupp.MonomialOrder.DegLex
import Mathlib.Data.Finsupp.MonomialOrder
import Mathlib.Data.DFinsupp.WellFounded
import Mathlib.Combinatorics.Enumerative.DoubleCounting
import Mathlib.Algebra.Polynomial.Taylor
import Mathlib.Algebra.Polynomial.RingDivision
import Mathlib.Algebra.Polynomial.Eval.Coeff
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
import Mathlib.Algebra.MvPolynomial.Division
import Mathlib.Algebra.Lie.NonUnitalNonAssocAlgebra
import Mathlib.Algebra.Lie.Derivation.Basic
import Mathlib.Algebra.GroupWithZero.Torsion
import Mathlib.Algebra.GradedMulAction
import Mathlib.Algebra.DirectSum.Ring
import Mathlib.Algebra.DirectSum.Internal
import Mathlib.Algebra.DirectSum.Algebra
import Mathlib.Algebra.CharP.Quotient
import Mathlib.Algebra.Order.GroupWithZero.Canonical
import Mathlib.RingTheory.Valuation.Basic
import Definitions.Def_Yukon_01021eded3220e2800cfca71
import Definitions.Def_Yukon_db9e62887577419e408bc32c
import Definitions.Def_Yukon_7bdfb5c7976bc55dd3e2bf3e
import Definitions.Def_Yukon_196ff1de7425c8d8df8d3a11
import Definitions.Def_Yukon_07bb1fdf83fc478e7c5449e7
import Definitions.Def_Yukon_867f9fe91b5fcd4219c71561
import Definitions.Def_Yukon_5ead00dac98325c22e6d5e52
set_option backward.isDefEq.respectTransparency.types false
namespace ProximityPrize.SubmissionLower.AsymmetricChainPolynomial80889
end AsymmetricChainPolynomial80889
end SubmissionLower
end ProximityPrize
namespace ProximityPrize.SubmissionLower.BoundaryTailSharedDegreeBudget
end BoundaryTailSharedDegreeBudget
end SubmissionLower
end ProximityPrize
namespace ProximityPrize.SubmissionLower.Lower80889.Counting
end Counting
end Lower80889
end SubmissionLower
end ProximityPrize
namespace ProximityPrize.SubmissionLower.LocatorPhase6800Oracle
end LocatorPhase6800Oracle
end SubmissionLower
end ProximityPrize
namespace ProximityPrize.SubmissionLower.LocatorBatchPhase6800
end LocatorBatchPhase6800
end SubmissionLower
end ProximityPrize
namespace ProximityPrize.SubmissionLower.LocatorFactorAggregate
end LocatorFactorAggregate
end SubmissionLower
end ProximityPrize
namespace ProximityPrize.SubmissionLower.LocatorBatchProductRoute
end LocatorBatchProductRoute
end SubmissionLower
end ProximityPrize
namespace ProximityPrize.SubmissionLower.RCN180
end RCN180
end SubmissionLower
end ProximityPrize
namespace ProximityPrize.SubmissionLower.RCN267
end RCN267
end SubmissionLower
end ProximityPrize
namespace ProximityPrize.SubmissionLower.RCN286
end RCN286
end SubmissionLower
end ProximityPrize
namespace ProximityPrize.SubmissionLower.RCN319
end RCN319
end SubmissionLower
end ProximityPrize
namespace ProximityPrize.SubmissionLower.RCN266
end RCN266
end SubmissionLower
end ProximityPrize
namespace ProximityPrize.SubmissionLower.RCN260
end RCN260
end SubmissionLower
end ProximityPrize
namespace ProximityPrize.SubmissionLower.RCN243
end RCN243
end SubmissionLower
end ProximityPrize
namespace ProximityPrize.SubmissionLower.RCN238
end RCN238
end SubmissionLower
end ProximityPrize
namespace ProximityPrize.SubmissionLower.RCN234
end RCN234
end SubmissionLower
end ProximityPrize
namespace ProximityPrize.SubmissionLower.RCN174
end RCN174
end SubmissionLower
end ProximityPrize
namespace ProximityPrize.SubmissionLower.RCN167
end RCN167
end SubmissionLower
end ProximityPrize
namespace ProximityPrize.SubmissionLower.RCN156
end RCN156
end SubmissionLower
end ProximityPrize
namespace ProximityPrize.SubmissionLower.RCN140
end RCN140
end SubmissionLower
end ProximityPrize
namespace ProximityPrize.SubmissionLower.RCN130
end RCN130
end SubmissionLower
end ProximityPrize
namespace ProximityPrize.SubmissionLower.RCN100
end RCN100
end SubmissionLower
end ProximityPrize
namespace ProximityPrize.SubmissionLower.RCN095
end RCN095
end SubmissionLower
end ProximityPrize
namespace ProximityPrize.SubmissionLower.RCN081
end RCN081
end SubmissionLower
end ProximityPrize
namespace ProximityPrize.SubmissionLower.RCN071
end RCN071
end SubmissionLower
end ProximityPrize
namespace ProximityPrize.Benchmark
end Benchmark
end ProximityPrize
namespace ProximityPrize.SubmissionLower.Lower80889.Budgets
open ProximityPrize.Benchmark
open scoped Classical BigOperators
open RCN071 RCN081 RCN095 RCN100 RCN130 RCN140 RCN156 RCN167 RCN174 RCN234 RCN238 RCN243 RCN260 RCN266 RCN319
open RCN286 RCN267 RCN180 LocatorBatchProductRoute
open LocatorFactorAggregate LocatorBatchPhase6800 LocatorPhase6800Oracle Counting BoundaryTailSharedDegreeBudget AsymmetricChainPolynomial80889
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000
attribute [local instance] _root_.ProximityPrize.SubmissionLower.Lower80889.Budgets.instDecidableEqK
attribute [local instance] _root_.ProximityPrize.SubmissionLower.Lower80889.Budgets.instDecidableEqI
theorem _root_.solution (H Q : P4) (hH : H ≠ 0) (hQ : Q ≠ 0)
    (hbox : H*Q ∈ RCN100.globalCoefficientBox K 24288170 131071 35527 40)
    (hHbox : H ∈ RCN174.globalCoefficientBox K 24288170 131071 35527 40)
    (hQbox : Q ∈ RCN174.globalCoefficientBox K 24288170 131071 35527 40)
    (U : Finset (RegularIndex H)) (u0 u1 : I → K) (selected : K → Polynomial K)
    (Gamma Delta : Finset K) (inpH : Input u0 u1 selected Gamma) (inpQ : Input u0 u1 selected Delta)
    (hr : (regularAggregateFlag H U).all ≤ 37)
    (hy : middle (regularAggregateFlag H U) ≤ 175)
    (ht : total (regularAggregateFlag H U) ≤ 10714) :
    let p := regularAggregateFlag H U
    (∑ F : RegularIndex H, factorCharge F.1 selected Gamma) +
      (∑ F : RegularIndex Q, factorCharge F.1 selected Delta) ≤
      p.all*unit (middle p) (total p) p.all +
      (40-p.all)*unit (185-middle p) (35527-total p) (40-p.all) + 40*4502611644209  := by
  let p := regularAggregateFlag H U
  let N := (Finset.univ : Finset (RegularIndex H)) \ U
  have hb := aggregate_pair_caps H Q hH hQ hbox
  have hs := split_aggregate H U
  have hnR : (regularAggregateFlag H N).all ≤ 40-p.all := by dsimp only [p,N]; omega
  have hnY : middle (regularAggregateFlag H N) ≤ 185-middle p := by dsimp only [p,N]; omega
  have hnT : total (regularAggregateFlag H N) ≤ 35527-total p := by dsimp only [p,N]; omega
  have hqR : (regularAggregateFlag Q Finset.univ).all ≤ 40-p.all := by dsimp only [p]; omega
  have hqY : middle (regularAggregateFlag Q Finset.univ) ≤ 185-middle p := by dsimp only [p]; omega
  have hqT : total (regularAggregateFlag Q Finset.univ) ≤ 35527-total p := by dsimp only [p]; omega
  have hsum : (∑ F ∈ U, F.1.degreeOf 2) = p.all := by
    simp only [p, regularAggregateFlag, sumFlag_all, regularCumulativeFlag, originalCumulativeFlag_all]
  have hprodBox := RCN101.flag_box_to_ordinary K 24288170 131071 35527 40 (H*Q) hbox
  have hc := split_slope_charge (Finset.univ : Finset (RegularIndex H)) U
    (Finset.univ : Finset (RegularIndex Q)) (Finset.subset_univ _) (fun F => F.1) (fun F => F.1)
    H Q hH hQ (regularProduct_dvd_carrier H _) (regularProduct_dvd_carrier Q _)
    40 (unit (middle p) (total p) p.all + 4502611644209) (unit (185-middle p) (35527-total p) (40-p.all) + 4502611644209)
    (degreeOf_R_le_of_mem_box (H*Q) 24288170 131071 35527 40 hprodBox)
    (fun F => factorCharge F.1 selected Gamma) (fun F => factorCharge F.1 selected Delta)
    (fun F hF => by
      have hf := directFactor_data H F.1 hH 24288170 131071 35527 40 hHbox F.2
      have hd := factor_coordinates H U F hF
      exact factorCharge_le_unit inpH F.1 hf.1 hf.2.1 hf.2.2 _ _ _
        (hy.trans (by decide +kernel)) (ht.trans (by decide +kernel)) (hr.trans (by decide +kernel)) hd.1 hd.2.2 hd.2.1)
    (fun F hF => by
      have hf := directFactor_data H F.1 hH 24288170 131071 35527 40 hHbox F.2
      have hd := factor_coordinates H N F hF
      exact factorCharge_le_unit inpH F.1 hf.1 hf.2.1 hf.2.2 _ _ _
        (Nat.sub_le _ _) (Nat.sub_le _ _) (Nat.sub_le _ _)
        (hd.1.trans hnY) (hd.2.2.trans hnT) (hd.2.1.trans hnR))
    (fun F _ => by
      have hf := directFactor_data Q F.1 hQ 24288170 131071 35527 40 hQbox F.2
      have hd := factor_coordinates Q Finset.univ F (Finset.mem_univ _)
      exact factorCharge_le_unit inpQ F.1 hf.1 hf.2.1 hf.2.2 _ _ _
        (Nat.sub_le _ _) (Nat.sub_le _ _) (Nat.sub_le _ _)
        (hd.1.trans hqY) (hd.2.2.trans hqT) (hd.2.1.trans hqR))
  rw [hsum] at hc
  have hp : p.all + (40-p.all) = 40 := by dsimp only [p]; omega
  calc
    _ ≤ _ := hc
    _ = p.all*unit (middle p) (total p) p.all +
        (40-p.all)*unit (185-middle p) (35527-total p) (40-p.all) +
          (p.all+(40-p.all))*4502611644209 := by ring
    _ = _ := by rw [hp]
end
end Budgets
end Lower80889
end SubmissionLower
end ProximityPrize
