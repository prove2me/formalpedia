-- Prove2me | solution 1 for ProximityPrize.SubmissionLower.MovingFiberRetainedStage6811.retained_stage_bound_yukon_ed8ab9cbea25
-- status  : ACCEPTED   (prove)
-- author  : @yukon
-- created : 2026-10-02T21:46:35.899982+00:00
-- url     : https://prove2.me/submissions/944e1fa4-95f4-405b-847d-9866ead0ae6e

import Definitions.Def_Yukon_ca6ef1ca29b9483e7b8d8f20


import Theorems.Thm_ProximityPrize_SubmissionLower_HFreeFirstSlice6812_hfree_slice_charge_yukon_0c4d4c5f7c20
import Definitions.Def_Yukon_74ba13f07dc1a61561ec3e92



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
import Mathlib.Algebra.BigOperators.Field
import Definitions.Def_Yukon_9bc6354a39244d128eafc24b
import Definitions.Def_Yukon_9e01353f705b1903d07af3b0
import Definitions.Def_Yukon_52f7c2cb3790c155905697c9
import Definitions.Def_Yukon_5c9a7a9d17b650621345d8aa
import Definitions.Def_Yukon_910f7f29d27cb8bde8dfa124
import Definitions.Def_Yukon_196ff1de7425c8d8df8d3a11
import Definitions.Def_Yukon_07bb1fdf83fc478e7c5449e7
import Definitions.Def_Yukon_755f5ab5e1dfa660f8e11f09
import Definitions.Def_Yukon_867f9fe91b5fcd4219c71561
import Definitions.Def_Yukon_c64d4480230f512d8aedf66b
import Definitions.Def_Yukon_ef32f3d6934bd47f231d0d68
import Definitions.Def_Yukon_1cfb6b19fd8d8d5aca848f54
set_option backward.isDefEq.respectTransparency.types false
private abbrev ProximityPrize.SubmissionLower.HFreeFirstSlice6812.hfree_slice_charge := @ProximityPrize.SubmissionLower.HFreeFirstSlice6812.hfree_slice_charge_yukon_0c4d4c5f7c20
namespace ProximityPrize.SubmissionLower.MovingFiberThreeSources6811
end MovingFiberThreeSources6811
end SubmissionLower
end ProximityPrize
namespace ProximityPrize.SubmissionLower.CommonLinearChannels6807
end CommonLinearChannels6807
end SubmissionLower
end ProximityPrize
namespace ProximityPrize.SubmissionLower.BoundaryTailProvider
end BoundaryTailProvider
end SubmissionLower
end ProximityPrize
namespace ProximityPrize.SubmissionLower.LocatorHybridTailProvider
end LocatorHybridTailProvider
end SubmissionLower
end ProximityPrize
namespace ProximityPrize.SubmissionLower.LocatorHybridTransportC2
end LocatorHybridTransportC2
end SubmissionLower
end ProximityPrize
namespace ProximityPrize.SubmissionLower.LocatorHybridCellsC1
end LocatorHybridCellsC1
end SubmissionLower
end ProximityPrize
namespace ProximityPrize.SubmissionLower.LocatorHybridCells
end LocatorHybridCells
end SubmissionLower
end ProximityPrize
namespace ProximityPrize.SubmissionLower.RCN344
end RCN344
end SubmissionLower
end ProximityPrize
namespace ProximityPrize.SubmissionLower.RCN341
end RCN341
end SubmissionLower
end ProximityPrize
namespace ProximityPrize.SubmissionLower.RCN340
end RCN340
end SubmissionLower
end ProximityPrize
namespace ProximityPrize.SubmissionLower.RCN339
end RCN339
end SubmissionLower
end ProximityPrize
namespace ProximityPrize.SubmissionLower.RCN338
end RCN338
end SubmissionLower
end ProximityPrize
namespace ProximityPrize.SubmissionLower.RCN336
end RCN336
end SubmissionLower
end ProximityPrize
namespace ProximityPrize.SubmissionLower.RCN334
end RCN334
end SubmissionLower
end ProximityPrize
namespace ProximityPrize.SubmissionLower.RCN332
end RCN332
end SubmissionLower
end ProximityPrize
namespace ProximityPrize.SubmissionLower.RCN331
end RCN331
end SubmissionLower
end ProximityPrize
namespace ProximityPrize.SubmissionLower.RCN330
end RCN330
end SubmissionLower
end ProximityPrize
namespace ProximityPrize.SubmissionLower.RCN327
end RCN327
end SubmissionLower
end ProximityPrize
namespace ProximityPrize.SubmissionLower.RCN313
end RCN313
end SubmissionLower
end ProximityPrize
namespace ProximityPrize.SubmissionLower.RCN287
end RCN287
end SubmissionLower
end ProximityPrize
namespace ProximityPrize.SubmissionLower.RCN275
end RCN275
end SubmissionLower
end ProximityPrize
namespace ProximityPrize.SubmissionLower.RCN271
end RCN271
end SubmissionLower
end ProximityPrize
namespace ProximityPrize.SubmissionLower.RCN264
end RCN264
end SubmissionLower
end ProximityPrize
namespace ProximityPrize.SubmissionLower.RCN263
end RCN263
end SubmissionLower
end ProximityPrize
namespace ProximityPrize.SubmissionLower.RCN244
end RCN244
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
namespace ProximityPrize.SubmissionLower.RCN237
end RCN237
end SubmissionLower
end ProximityPrize
namespace ProximityPrize.SubmissionLower.RCN234
end RCN234
end SubmissionLower
end ProximityPrize
namespace ProximityPrize.SubmissionLower.RCN207
end RCN207
end SubmissionLower
end ProximityPrize
namespace ProximityPrize.SubmissionLower.RCN206
end RCN206
end SubmissionLower
end ProximityPrize
namespace ProximityPrize.SubmissionLower.RCN199
end RCN199
end SubmissionLower
end ProximityPrize
namespace ProximityPrize.SubmissionLower.RCN198
end RCN198
end SubmissionLower
end ProximityPrize
namespace ProximityPrize.SubmissionLower.RCN159
end RCN159
end SubmissionLower
end ProximityPrize
namespace ProximityPrize.SubmissionLower.RCN156
end RCN156
end SubmissionLower
end ProximityPrize
namespace ProximityPrize.SubmissionLower.RCN136
end RCN136
end SubmissionLower
end ProximityPrize
namespace ProximityPrize.SubmissionLower.RCN135
end RCN135
end SubmissionLower
end ProximityPrize
namespace ProximityPrize.SubmissionLower.RCN095
end RCN095
end SubmissionLower
end ProximityPrize
namespace ProximityPrize.SubmissionLower.RCN086
end RCN086
end SubmissionLower
end ProximityPrize
namespace ProximityPrize.SubmissionLower.RCN085
end RCN085
end SubmissionLower
end ProximityPrize
namespace ProximityPrize.SubmissionLower.RCN084
end RCN084
end SubmissionLower
end ProximityPrize
namespace ProximityPrize.SubmissionLower.RCN074
end RCN074
end SubmissionLower
end ProximityPrize
namespace ProximityPrize.SubmissionLower.RCN057
end RCN057
end SubmissionLower
end ProximityPrize
namespace ProximityPrize.SubmissionLower.RCN046
end RCN046
end SubmissionLower
end ProximityPrize
namespace ProximityPrize.SubmissionLower.RCN002
end RCN002
end SubmissionLower
end ProximityPrize
namespace ProximityPrize.SubmissionLower.MovingFiberRetainedStage6811
open scoped Classical BigOperators
open RCN002 RCN046 RCN057 RCN074 RCN084 RCN085 RCN086 RCN095 RCN135 RCN136 RCN156 RCN159
open RCN198 RCN199 RCN206 RCN207 RCN234 RCN237 RCN238 RCN243 RCN244 RCN263 RCN264 RCN271 RCN275
open RCN287 RCN313 RCN327 RCN330 RCN331 RCN332 RCN334 RCN336 RCN338 RCN339 RCN340 RCN341 RCN344
open LocatorHybridCells LocatorHybridCellsC1 LocatorHybridTransportC2 LocatorHybridTailProvider
open BoundaryTailProvider CommonLinearChannels6807 MovingFiberThreeSources6811
noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 100000
set_option maxRecDepth 100000
variable {K I : Type} [Field K]
variable {Gamma : Finset K} {x : I → K} {p : ℕ} {flag : FlagDegree}
  [CharP K p] [CharP (GenericField K) p] {errorCap : ℕ}
local notation "Ω" => GenericField K
attribute [local instance] _root_.ProximityPrize.SubmissionLower.MovingFiberRetainedStage6811.instDecidableEq_proximityPrize
attribute [local instance] _root_.ProximityPrize.SubmissionLower.MovingFiberRetainedStage6811.instDecidableEq_proximityPrize_1
theorem _root_.solution
    (t y r scale : ℕ) (hr3 : 3 ≤ r) (hb : r+2 ≤ y) (hyt : y ≤ t)
    (S : ResidualStage (polynomialEmbedding K) Gamma x p errorCap flag w (cellSupport t y r))
    (source : Fin 3 → Source S.F) (hscale : 0 < scale) (hscaleDiv : ∀ j, 3*(source j).d ∣ scale)
    (hfree : HFreeStage S)
    (hproper : ¬ S.G ∣ globalTailCut (polynomialEmbedding K) S.F (w+1))
    (hflagChar : flag.yz+flag.all < p ∧ flag.all < p ∧ flag.zOnly+flag.yz+flag.all < p)
    (hmixedRed : flagMixed flag (cellFirstTail t y r) unitZFlag < p)
    (hlinear : 2*(flag.zOnly+flag.yz+flag.all) < p)
    (hmovingGate : 2*(flag.zOnly+flag.yz+flag.all)*(t+1) < p)
    (hchar : 2*(w-1) < p)
    (hgate : errorCap+1 ≤ (cellNormal t y r).yz)
    (htangent : ∀ C : FirstTailComponent S,
      (∀ delay, globalTailCut (polynomialEmbedding K) S.F (w+1+delay) ∈ C.1) →
      (componentSeeds Ω S.G (globalTailCut (polynomialEmbedding K) S.F (w+1))
        (regularitySurface (polynomialEmbedding K) S.F) Gamma
        (selectedPoint (polynomialEmbedding K) S.selected) C).card ≤
        (errorCap+1)*(BoundaryTailReduced.reducedBudgetFamily S hproper hflagChar hmixedRed).yzCost C)
    (h2 : (2 : Ω) ≠ 0) (hfact : ∀ j, ((source j).k.factorial : Ω) ≠ 0)
    (hgood : ∀ gamma ∈ Gamma, ∀ j,
      MvPolynomial.eval (selectedPoint (polynomialEmbedding K) S.selected gamma)
        ((source j).leading (polynomialEmbedding K)) ≠ 0) :
    Gamma.card ≤ numerator source scale t y r flag / scale  := by
  classical
  let Ext := AlgebraicClosure (RatFunc Ω)
  letI : CharP Ext p := charP_of_injective_algebraMap (algebraMap Ω Ext).injective p
  have h2E : (2 : Ext) ≠ 0 := by
    simpa only [map_ofNat,map_zero] using (algebraMap Ω Ext).injective.ne h2
  have hfactE (j : Fin 3) : ((source j).k.factorial : Ext) ≠ 0 := by
    simpa only [map_natCast,map_zero] using (algebraMap Ω Ext).injective.ne (hfact j)
  let base := BoundaryTailReduced.reducedBaseOrd S hproper hflagChar hmixedRed
  let Uold := BoundaryTailReduced.reducedUnitFamily S hproper hflagChar hmixedRed
  let unit := unitFamilyOfCongruentCut (ordinary_sub_reducedFirstCut_dvd S) Uold base
  let Bfam := BoundaryTailReduced.reducedBudgetFamily S hproper hflagChar hmixedRed
  let common := ReducedCommonLinear6807.original_common S hproper hflagChar hmixedRed
  let active : Finset (FirstTailComponent S) := Finset.univ.filter
    (fun C => ∀ j : Fin 3, (source j).leading (polynomialEmbedding K) ∉ C.1)
  have hlead (C : active) (j : Fin 3) : (source j).leading (polynomialEmbedding K) ∉ C.val.1 :=
    (Finset.mem_filter.mp C.property).2 j
  have Hsupport : ResidualSupportData (cellSupport t y r) S.F :=
    ⟨S.surface_s_weight,S.surface_ys_weight,S.surface_total_weight⟩
  have hs : cellS r+2 = r := by dsimp [cellS]; omega
  have hys : cellB y r+cellS r+3 = r+(y-r) := by dsimp [cellB,cellS]; omega
  have htot : cellA t y+cellB y r+cellS r+3 = r+(y-r)+(t-y) := by dsimp [cellA,cellB,cellS]; omega
  have hR : WeightBound residualSWeights S.F (r : ℤ) := by
    apply Or.inr
    exact_mod_cast (show wt residualSWeights S.F ≤ r by
      simpa only [cellSupport,RCN198.support,hs] using Hsupport.s_weight)
  have hYR : WeightBound residualYSWeights S.F ((r+(y-r) : ℕ) : ℤ) := by
    apply Or.inr
    exact_mod_cast (show wt residualYSWeights S.F ≤ r+(y-r) by
      simpa only [cellSupport,RCN198.support,hys] using Hsupport.ys_weight)
  have hAll : WeightBound residualTotalWeights S.F ((r+(y-r)+(t-y) : ℕ) : ℤ) := by
    apply Or.inr
    exact_mod_cast (show wt residualTotalWeights S.F ≤ r+(y-r)+(t-y) by
      simpa only [cellSupport,RCN198.support,htot] using Hsupport.total_weight)
  have hgates : 2*(flag.zOnly+flag.yz+flag.all)*(cellA t y+(cellB y r+1)+(cellS r+3)) < p := by
    have he : cellA t y+(cellB y r+1)+(cellS r+3) = t+1 := by dsimp [cellA,cellB,cellS]; omega
    simpa only [he] using hmovingGate
  have hdiv1 (j : Fin 3) : (source j).d ∣ scale := (Dvd.intro_left 3 rfl).trans (hscaleDiv j)
  obtain ⟨budget,hcost,hmoving⟩ := MovingFiberDegreeSum6811.exists_first_tail_budget (E := Ext)
    (polynomialEmbedding K) S.F source scale hscale hdiv1 S.G flag (cellFirstTail t y r)
    S.irreducible_G.ne_zero S.G_dvd_surface S.flag_support
    (cellA t y) (cellB y r) (cellS r) w (by norm_num [w])
    Hsupport.coordinate_bounds.2.1 Hsupport.ys_weight Hsupport.total_weight p hlinear hgates h2E hfactE
    base unit active (fun C hC j => (Finset.mem_filter.mp hC).2 j)
  have hcost' (C : FirstTailComponent S) :
      (budget C).zCost = Bfam.zCost C ∧ (budget C).yzCost = Bfam.yzCost C ∧ (budget C).allCost = Bfam.allCost C := by
    obtain ⟨hz,hy,ha⟩ := hcost C
    obtain ⟨ez,ey,ea⟩ := unitFamilyOfCongruentCut_costs (ordinary_sub_reducedFirstCut_dvd S) Uold base C
    exact ⟨hz.trans ez,hy.trans ey,ha.trans ea⟩
  have heq (f : FlagDegree) (C : FirstTailComponent S) :
      unit.toPrimeFlagBudgetFamily.weightedCost f C = Bfam.weightedCost f C := by
    obtain ⟨ez,ey,ea⟩ := unitFamilyOfCongruentCut_costs (ordinary_sub_reducedFirstCut_dvd S) Uold base C
    change unit.toPrimeFlagBudgetFamily.zCost C = Bfam.zCost C at ez
    change unit.toPrimeFlagBudgetFamily.yzCost C = Bfam.yzCost C at ey
    change unit.toPrimeFlagBudgetFamily.allCost C = Bfam.allCost C at ea
    unfold PrimeFlagBudgetFamily.weightedCost
    rw [ez,ey,ea]
  let mu := fun C : FirstTailComponent S => localMultiplicity (loosenStageGeneral S)
    (canonicalLocalDVRFamily (loosenStageGeneral S) hproper) C
  let first := hfreeFirst t y r
  let normal := cellNormal t y r
  let projection : (j : Fin 3) → (C : FirstTailComponent S) → Coordinate Ω (CoordinateField Ω C.1) :=
    ![unit.zProjection,unit.yzProjection,unit.allProjection]
  let ell := channel S hproper hflagChar hmixedRed
  have hell (j : Fin 3) : PolynomialInFlag (MovingFiberThreeSources6811.direction j) (ell j) := by
    fin_cases j
    · exact linearZ_in_flag
    · exact linearU_in_flag _
    · exact linearA_in_flag _ _
  have hvalue (j : Fin 3) (C : FirstTailComponent S) :
      coordinateValue Ω (CoordinateField Ω C.1) (projection j C) = coordinateEvaluation Ω C.1 (ell j) := by
    fin_cases j
    · exact common_z_value unit C
    · exact common_u_value unit common C
    · exact common_a_value unit common C
  have hnormal (j : Fin 3) :
      scale*(∑ C : active, mu C.val*coordinateDegree Ω (CoordinateField Ω C.val.1) (projection j C.val)) ≤
      scale/3*flagMixed flag first (MovingFiberThreeSources6811.direction j) +
        4*(w+1)*(scale/(3*(source j).d))*flagMixed flag (MovingFiberThreeSources6811.direction j) (source j).flag := by
    have hq : (MovingFiberThreeSources6811.direction j).zOnly+(MovingFiberThreeSources6811.direction j).yz+
        (MovingFiberThreeSources6811.direction j).all = 1 := by fin_cases j <;> rfl
    have h := ActualGenericChannel6807.first_cut_for_coordinate_channel (E := Ext)
      (loosenStageGeneral S) hproper (fun C : active => C.val) Subtype.val_injective
      (ell j) (MovingFiberThreeSources6811.direction j) (hell j)
      (fun C => projection j C.val) (fun C => hvalue j C.val)
      hflagChar.2.2 (by rw [hq,mul_one]; exact hlinear) _ (fun C => hlead C j)
      _ _ _ _ _ (HFreeFirstSlice6812.hfree_slice_charge (E := Ext) (loosenStageGeneral S) hproper
        (ell j) (source j).P (source j).B (source j).U (source j).T (source j).s (source j).k (source j).n0
        (source j).hS (source j).hshape (source j).hBU (source j).hUT (source j).hdn (source j).hB
        (source j).hn (source j).hdiv h2E (hfactE j) r (y-r) (t-y) hr3 (by omega) hR hYR hAll
        unitAllFlag (hfree hproper hflagChar hmixedRed j))
    have hexp : flagMixed flag (MovingFiberThreeSources6811.direction j)
        ((source j).d • first+(4*(w+1)) • (source j).flag) =
        (source j).d*flagMixed flag first (MovingFiberThreeSources6811.direction j) +
          4*(w+1)*flagMixed flag (MovingFiberThreeSources6811.direction j) (source j).flag := by
      simp only [flagMixed,add_zOnly,add_yz,add_all,nsmul_zOnly,nsmul_yz,nsmul_all]
      ring
    change 3*(source j).d*(∑ C : active, mu C.val*coordinateDegree Ω (CoordinateField Ω C.val.1) (projection j C.val)) ≤
      flagMixed flag (MovingFiberThreeSources6811.direction j) ((source j).d • first+(4*(w+1)) • (source j).flag) at h
    rw [hexp] at h
    obtain ⟨m,hm⟩ := hscaleDiv j
    have hd0 : 0 < 3*(source j).d := by simp only [Source.d]; omega
    have h3 : scale/3 = (source j).d*m := by
      rw [hm,Nat.mul_assoc,Nat.mul_div_cancel_left _ (by norm_num)]
    have h3d : scale/(3*(source j).d) = m := by rw [hm,Nat.mul_div_cancel_left _ hd0]
    rw [h3,h3d,hm]
    calc
      _ = m*(3*(source j).d*(∑ C : active, mu C.val*coordinateDegree Ω (CoordinateField Ω C.val.1) (projection j C.val))) := by ring
      _ ≤ m*((source j).d*flagMixed flag first (MovingFiberThreeSources6811.direction j) +
          4*(w+1)*flagMixed flag (MovingFiberThreeSources6811.direction j) (source j).flag) :=
        Nat.mul_le_mul_left m h
      _ = _ := by ring
  have hnormalSum : scale*(∑ C ∈ active, mu C*Bfam.weightedCost normal C) ≤
      scale/3*flagMixed flag first normal +
        ∑ j : Fin 3, 4*(w+1)*weight normal j*(scale/(3*(source j).d))*flagMixed flag (MovingFiberThreeSources6811.direction j) (source j).flag := by
    have h := Finset.sum_le_sum (fun j (_ : j ∈ (Finset.univ : Finset (Fin 3))) =>
      Nat.mul_le_mul_left (weight normal j) (hnormal j))
    have hsum : (∑ C ∈ active, mu C*Bfam.weightedCost normal C) =
        ∑ C : active, mu C.val*unit.toPrimeFlagBudgetFamily.weightedCost normal C.val := by
      calc
        _ = ∑ C ∈ active, mu C*unit.toPrimeFlagBudgetFamily.weightedCost normal C := by
          apply Finset.sum_congr rfl
          intro C _
          rw [heq]
        _ = _ := (Finset.sum_coe_sort active (fun C => mu C*unit.toPrimeFlagBudgetFamily.weightedCost normal C)).symm
    rw [hsum]
    have hl : scale*(∑ C : active, mu C.val*unit.toPrimeFlagBudgetFamily.weightedCost normal C.val) =
        ∑ j : Fin 3, weight normal j*(scale*∑ C : active, mu C.val*
          coordinateDegree Ω (CoordinateField Ω C.val.1) (projection j C.val)) := by
      rw [Fin.sum_univ_three]
      change scale*(∑ C : active, mu C.val*unit.toPrimeFlagBudgetFamily.weightedCost normal C.val) =
        normal.zOnly*(scale*∑ C : active, mu C.val*coordinateDegree Ω (CoordinateField Ω C.val.1) (unit.zProjection C.val)) +
        normal.yz*(scale*∑ C : active, mu C.val*coordinateDegree Ω (CoordinateField Ω C.val.1) (unit.yzProjection C.val)) +
        normal.all*(scale*∑ C : active, mu C.val*coordinateDegree Ω (CoordinateField Ω C.val.1) (unit.allProjection C.val))
      have hp (C : active) : mu C.val*unit.toPrimeFlagBudgetFamily.weightedCost normal C.val =
          normal.zOnly*(mu C.val*coordinateDegree Ω (CoordinateField Ω C.val.1) (unit.zProjection C.val)) +
          normal.yz*(mu C.val*coordinateDegree Ω (CoordinateField Ω C.val.1) (unit.yzProjection C.val)) +
          normal.all*(mu C.val*coordinateDegree Ω (CoordinateField Ω C.val.1) (unit.allProjection C.val)) := by
        simp only [PrimeFlagBudgetFamily.weightedCost,AdaptiveUnitProjectionFamily.toPrimeFlagBudgetFamily,
          AdaptiveUnitPoleBudget.toPrimeFlagBudgetFamily,AdaptiveUnitProjectionFamily.toAdaptiveUnitPoleBudget]
        ring
      simp_rw [hp]
      simp only [Finset.sum_add_distrib,← Finset.mul_sum]
      ring
    have hmixed : (∑ j : Fin 3, weight normal j*flagMixed flag first (MovingFiberThreeSources6811.direction j)) =
        flagMixed flag first normal := by
      simp only [Fin.sum_univ_three,weight,MovingFiberThreeSources6811.direction,
        Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail,Function.comp_apply,Matrix.cons_val_succ,
        flagMixed,unitZFlag,unitYZFlag,unitAllFlag]
      ring
    have hr : scale/3*flagMixed flag first normal +
        (∑ j : Fin 3, 4*(w+1)*weight normal j*(scale/(3*(source j).d))*flagMixed flag (MovingFiberThreeSources6811.direction j) (source j).flag) =
        ∑ j : Fin 3, weight normal j*(scale/3*flagMixed flag first (MovingFiberThreeSources6811.direction j) +
          4*(w+1)*(scale/(3*(source j).d))*flagMixed flag (MovingFiberThreeSources6811.direction j) (source j).flag) := by
      rw [← hmixed,Finset.mul_sum]
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro j _
      ring
    rw [hl,hr]
    exact h
  let moveNum := ∑ j : Fin 3, weight (rawFirstFlag t y r) j*(scale/(source j).d)*
    flagMixed flag (MovingFiberThreeSources6811.direction j) (source j).flag
  have hmovingScaled : scale*(∑ C ∈ active, (budget C).movingCost) ≤ moveNum := by
    exact (Nat.mul_le_mul_left scale hmoving).trans (by
      simpa only [moveNum,rawFirstFlag,Nat.mul_comm] using Nat.div_mul_le_self moveNum scale)
  have hjointScaled : scale*(∑ C ∈ active, (mu C*Bfam.weightedCost normal C+65539*(budget C).movingCost)) ≤
      numerator source scale t y r flag := by
    have h := Nat.add_le_add hnormalSum (Nat.mul_le_mul_left 65539 hmovingScaled)
    convert h using 1
    · simp only [Finset.sum_add_distrib,← Finset.mul_sum]
      ring
    · simp only [numerator,moveNum,first,normal,Nat.add_mul,Finset.sum_add_distrib,Finset.mul_sum,Nat.mul_assoc]
      ring
  have hjoint : (∑ C ∈ active, (mu C*Bfam.weightedCost normal C+65539*(budget C).movingCost)) ≤
      numerator source scale t y r flag/scale := by
    apply (Nat.le_div_iff_mul_le hscale).mpr
    simpa only [Nat.mul_comm] using hjointScaled
  have hinactive : ∀ C : FirstTailComponent S, C ∉ active →
      (componentSeeds Ω S.G (globalTailCut (polynomialEmbedding K) S.F (w+1))
        (regularitySurface (polynomialEmbedding K) S.F) Gamma
        (selectedPoint (polynomialEmbedding K) S.selected) C).card = 0 := by
    intro C hC
    have hex : ∃ j : Fin 3, (source j).leading (polynomialEmbedding K) ∈ C.1 := by
      simpa only [active,Finset.mem_filter,Finset.mem_univ,true_and,not_forall,not_not] using hC
    obtain ⟨j,hj⟩ := hex
    exact SecondJetExceptionalComponents.component_empty_of_nonvanishing _ _ _
      ((source j).leading (polynomialEmbedding K)) Gamma _ C hj (fun gamma hgamma => hgood gamma hgamma j)
  obtain ⟨provider⟩ := BoundaryTailJointBudget6807.exists_provider_of_joint_curve_budget
    t y r hr3 hb hyt hchar S hproper (cellFirstTail t y r) Bfam base budget hcost'
    active (numerator source scale t y r flag/scale) hinactive hjoint hgate htangent
  exact stage_card_le_divisorBound S provider
end
end MovingFiberRetainedStage6811
end SubmissionLower
end ProximityPrize
