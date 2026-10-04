-- Prove2me | solution 1 for ProximityPrize.SubmissionLower.HFreeFirstSlice6812.hfree_source_pole_mass_yukon_c5c268d51005
-- status  : ACCEPTED   (prove)
-- author  : @yukon
-- created : 2026-10-02T17:38:16.924651+00:00
-- url     : https://prove2.me/submissions/c9a13e97-ee0d-46c2-8a63-53bed7b0c343

/-
H-free first cut. The only new input is `HFreeSliceBudget`; it replaces the
first-cut local pole bound, and everything else reuses the 6807 chain.
-/



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
import Definitions.Def_Yukon_1a73be96c34fef79c5d93dc9
import Definitions.Def_Yukon_dbb021723d5dd757e7cd34c2
import Definitions.Def_Yukon_aa49d06014b5907015f56d9e
import Definitions.Def_Yukon_74ba13f07dc1a61561ec3e92
import Definitions.Def_Yukon_196ff1de7425c8d8df8d3a11
import Definitions.Def_Yukon_07bb1fdf83fc478e7c5449e7
import Definitions.Def_Yukon_755f5ab5e1dfa660f8e11f09
import Definitions.Def_Yukon_867f9fe91b5fcd4219c71561
import Definitions.Def_Yukon_d6a80e883014f27d904e1d8e
set_option backward.isDefEq.respectTransparency.types false
namespace ProximityPrize.SubmissionLower.ActualFirstCutPole6807
end ActualFirstCutPole6807
end SubmissionLower
end ProximityPrize
namespace ProximityPrize.SubmissionLower.SecondJetClearedHelper
end SecondJetClearedHelper
end SubmissionLower
end ProximityPrize
namespace ProximityPrize.SubmissionLower.SecondJetCoefficients
end SecondJetCoefficients
end SubmissionLower
end ProximityPrize
namespace ProximityPrize.SubmissionLower.SecondJetSupport
end SecondJetSupport
end SubmissionLower
end ProximityPrize
namespace ProximityPrize.SubmissionLower.RCN341
end RCN341
end SubmissionLower
end ProximityPrize
namespace ProximityPrize.SubmissionLower.RCN313
end RCN313
end SubmissionLower
end ProximityPrize
namespace ProximityPrize.SubmissionLower.RCN248
end RCN248
end SubmissionLower
end ProximityPrize
namespace ProximityPrize.SubmissionLower.RCN244
end RCN244
end SubmissionLower
end ProximityPrize
namespace ProximityPrize.SubmissionLower.RCN234
end RCN234
end SubmissionLower
end ProximityPrize
namespace ProximityPrize.SubmissionLower.RCN208
end RCN208
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
namespace ProximityPrize.SubmissionLower.RCN134
end RCN134
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
namespace ProximityPrize.SubmissionLower.RCN074
end RCN074
end SubmissionLower
end ProximityPrize
namespace ProximityPrize.SubmissionLower.RCN055
end RCN055
end SubmissionLower
end ProximityPrize
namespace ProximityPrize.SubmissionLower.RCN007
end RCN007
end SubmissionLower
end ProximityPrize
namespace ProximityPrize.SubmissionLower.RCN006
end RCN006
end SubmissionLower
end ProximityPrize
namespace ProximityPrize.SubmissionLower.RCN005
end RCN005
end SubmissionLower
end ProximityPrize
namespace ProximityPrize.SubmissionLower.RCN002
end RCN002
end SubmissionLower
end ProximityPrize
namespace ProximityPrize.SubmissionLower.HFreeFirstSlice6812
open RCN057 (WeightBound)
open RCN204 (flagPole)
open RCN026 (Place)
open scoped Classical BigOperators WithZero
open RCN002 RCN005 RCN006 RCN007 RCN055 RCN074 RCN086 RCN095 RCN134 RCN135 RCN136
open RCN156 RCN208 RCN234 RCN244 RCN248 RCN313 RCN341
open SecondJetSupport SecondJetCoefficients SecondJetClearedHelper
open ActualFirstCutPole6807
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 12000000
set_option synthInstance.maxHeartbeats 500000
local notation "w" => RCN326.w
section Slice
variable {K E : Type} [Field K] [Field E] [IsAlgClosed E]
/-- H6: the H-free analogue of `FirstSlicePoleBudget6807.actual_first_source_pole_mass`. -/
theorem _root_.solution
    (phi : Polynomial K →+* E) (F : MvPolynomial (Fin 4) K)
    (C : Ideal (MvPolynomial (Fin 3) E)) [C.IsPrime]
    (base : SeparableLiteralCoordinate C)
    (P : Poly (K := K)) (B U T s k n0 : ℕ)
    (hS : ∀ e ∈ P.support, e 1 ≤ s)
    (hP : ∀ e ∈ P.support, 2*e 1+e 3 ≤ B ∧ e 1+e 2+e 3 ≤ U ∧
      e 1+e 2+e 3+e 4 ≤ T)
    (hBU : B ≤ U) (hUT : U ≤ T) (hdn : k+1 ≤ n0)
    (hB : 2*(n0-(k+1)) ≤ B) (hn : n0 ≤ (asS P).natDegree)
    (hF : surfaceMap phi F ∈ C)
    (hH : surfaceMap phi (polyH K F) ∉ C)
    (hlead : surfaceMap phi (asS P).leadingCoeff ∉ C)
    (hdiv : ∀ j ≤ k, F ∣ helper P F (s-j) j)
    (h2 : (2 : E) ≠ 0) (hfact : (k.factorial : E) ≠ 0)
    (r v z : ℕ) (hr : 2 ≤ r) (hv : 1 ≤ v)
    (hR : WeightBound residualSWeights F (r : ℤ))
    (hYR : WeightBound residualYSWeights F ((r+v : ℕ) : ℤ))
    (hAll : WeightBound residualTotalWeights F ((r+v+z : ℕ) : ℤ))
    (C0 : FlagDegree) (hbudget : HFreeSliceBudget phi F C C0) (CX CV : ℕ)
    (hXbudget : ∀ W : Finset (Place E (CoordinateField E C)),
      (∑ nu ∈ W, flagPole nu.val (coordinate E C) (hfreeFlag r v z C0)) ≤ (CX : ℤ))
    (hVbudget : ∀ W : Finset (Place E (CoordinateField E C)),
      (∑ nu ∈ W, flagPole nu.val (coordinate E C)
        (SecondJetRelaxedFlag.budgetFlag B U T (k+1) n0)) ≤ (CV : ℤ))
    (W : Finset (Place E (CoordinateField E C))) :
    ((3*(k+1) : ℕ) : ℤ) * (∑ nu ∈ W, RCN187.poleOrder nu.val
      (SecondJetComponentRoots.coefficientMap phi C (baseNumerator F (w-1)) /
        SecondJetComponentRoots.coefficientMap phi C (polyH K F)^(2*w-1))) ≤
      ((k+1 : ℕ) : ℤ)*(CX : ℤ)+((4*(w+1) : ℕ) : ℤ)*(CV : ℤ)  := by
  letI := polynomialBaseAlgebra E C base.index
  letI := rationalBaseAlgebra E C base.index base.transcendental
  letI := polynomialBaseScalarTower E C base.index
  letI := polynomialRationalScalarTower E C base.index base.transcendental
  letI := rationalBaseScalarTower E C base.index base.transcendental
  letI : FiniteDimensional (RatFunc E) (CoordinateField E C) := base.finite
  letI : Algebra.IsSeparable (RatFunc E) (CoordinateField E C) := base.separable
  let L := CoordinateField E C
  let ev := SecondJetComponentRoots.coefficientMap phi C
  let H := ev (polyH K F)
  let sigma := ev (polyG K F)/H
  let theta := fun nu : Place E L =>
    max (2*flagPole nu.val (coordinate E C) unitAllFlag)
      (flagPole nu.val (coordinate E C) unitYZFlag + RCN187.poleOrder nu.val sigma)
  let Hf : FlagDegree := ⟨z,v,r-1⟩
  have hHne : H ≠ 0 := by
    intro hz
    apply hH
    exact (SecondJetComponentRoots.evaluation_zero_iff C _).mp hz
  -- the moving mass, exactly as in `actual_first_source_pole_mass`
  have hdeg := SecondJetComponentRoots.degree_retained phi C P hlead
  have hroot := SecondJetComponentRoots.roots_retained phi C P F s k hS
    hF hH hlead hdiv h2 hfact
  have hdegree : n0 ≤ (SecondJetComponentRoots.componentPolynomial phi C P).natDegree := by
    rw [hdeg.2]
    exact hn
  have hs := SecondJetRelaxedFlag.moving_bound
    (MvPolynomial.map (phi.comp Polynomial.C) P) (phi Polynomial.X)
    B U T (k+1) n0 hBU hUT hdn hB
    (SecondJetSurfaceMap.mapped_support_bounds _ P B U T hP)
    (coordinate E C) (SecondJetComponentRoots.componentPolynomial phi C P)
    (SecondJetComponentRoots.coefficients phi C P) hdeg.1 hdegree
    (RCN064.movingRatio C (surfaceMap phi (polyH K F))
      (surfaceMap phi (polyG K F))/2) hroot (CV : ℤ) hVbudget W
  have hsource : ((k+1 : ℕ) : ℤ)*(∑ nu ∈ W, theta nu) ≤ (CV : ℤ) := by
    simpa only [SecondJetPoleScaling.pole_half _ h2, theta, sigma, H, ev,
      SecondJetComponentRoots.coefficientMap, RCN064.movingRatio,
      RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom] using hs
  have htarget : (∑ nu ∈ W, RCN064.movingPoleTarget C (surfaceMap phi (polyH K F))
      (surfaceMap phi (polyG K F)) nu) = ∑ nu ∈ W, theta nu := by
    apply Finset.sum_congr rfl
    intro nu _
    simp only [theta, RCN204.flagPole_unitAll, RCN204.flagPole_unitYZ]
    rfl
  -- zeros of `H` are bounded by its poles, hence by its flag
  let Pl := RCN026.placesFor E L H hHne
  have hHF := (BoundaryTailAlgebra.boundary_surfaceMap_flags phi F r v z hr hv hR hYR hAll).1
  have hpoleH (nu : Place E L) :
      RCN346.poleOrder E L nu H ≤ flagPole nu.val (coordinate E C) Hf := by
    apply pole_le_of_value_le nu.val _ _ (RCN204.flagPole_nonneg _ _ _)
    have h := RCN204.valuation_eval_le_flag nu.val (algebraMap E L)
      (RCN344.constant_value_le_one E L nu) (coordinate E C) Hf _ hHF
    simpa only [H, ev, SecondJetComponentRoots.coefficientMap,
      coordinateEvaluation_eq_aeval, MvPolynomial.aeval_eq_eval₂Hom,
      RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom] using h
  have hzero : (∑ nu ∈ W, RCN026.zeroOrder E L nu H) ≤
      ∑ nu ∈ Pl, flagPole nu.val (coordinate E C) Hf := by
    have hout : ∀ nu ∈ W.filter (fun nu => nu ∉ Pl), RCN026.zeroOrder E L nu H = 0 := by
      intro nu hnu
      have hno : RCN026.order E L nu H = 0 := by
        by_contra hne
        exact (Finset.mem_filter.mp hnu).2 (RCN026.placesFor_covers E L H hHne nu hne)
      simp only [RCN026.zeroOrder, hno, max_self]
    calc
      _ = (∑ nu ∈ W.filter (fun nu => nu ∈ Pl), RCN026.zeroOrder E L nu H) +
          ∑ nu ∈ W.filter (fun nu => nu ∉ Pl), RCN026.zeroOrder E L nu H :=
        (Finset.sum_filter_add_sum_filter_not W _ _).symm
      _ = ∑ nu ∈ W.filter (fun nu => nu ∈ Pl), RCN026.zeroOrder E L nu H := by
        rw [Finset.sum_eq_zero hout, add_zero]
      _ ≤ ∑ nu ∈ Pl, RCN026.zeroOrder E L nu H :=
        Finset.sum_le_sum_of_subset_of_nonneg
          (fun nu hnu => (Finset.mem_filter.mp hnu).2)
          (fun nu _ _ => RCN026.zeroOrder_nonneg E L nu H)
      _ = ∑ nu ∈ Pl, RCN346.poleOrder E L nu H := RCN026.sum_placesFor_zero_eq_pole E L H hHne
      _ ≤ _ := Finset.sum_le_sum (fun nu _ => hpoleH nu)
  -- the X-budget on `W ∪ Pl` covers both the `H` and the `C0` parts
  have hX := hXbudget (W ∪ Pl)
  have hXsplit : 2*((w+1 : ℕ) : ℤ)*(∑ nu ∈ Pl, flagPole nu.val (coordinate E C) Hf) +
      3*(∑ nu ∈ W, flagPole nu.val (coordinate E C) C0) ≤ (CX : ℤ) := by
    refine le_trans ?_ hX
    simp only [hfreeFlag, RCN204.flagPole_add, RCN204.flagPole_nsmul, Finset.sum_add_distrib,
      ← Finset.mul_sum]
    have h1 := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_union_right (s₁ := W) (s₂ := Pl))
      (fun nu _ _ => RCN204.flagPole_nonneg nu.val (coordinate E C) Hf)
    have h2 := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_union_left (s₁ := W) (s₂ := Pl))
      (fun nu _ _ => RCN204.flagPole_nonneg nu.val (coordinate E C) C0)
    push_cast
    nlinarith
  have hb := hbudget.pole_le W
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at hb
  rw [htarget] at hb
  push_cast at hb hsource ⊢
  have hk : (0 : ℤ) ≤ (k : ℤ)+1 := by positivity
  have hw : (0 : ℤ) ≤ (w : ℤ)+1 := by positivity
  have e1 := mul_le_mul_of_nonneg_left hb hk
  have e2 := mul_le_mul_of_nonneg_left hsource (mul_nonneg (by norm_num : (0 : ℤ) ≤ 4) hw)
  have e3 := mul_le_mul_of_nonneg_left hzero (mul_nonneg hk (mul_nonneg (by norm_num : (0 : ℤ) ≤ 2) hw))
  have e4 := mul_le_mul_of_nonneg_left hXsplit hk
  push_cast at e4
  nlinarith
end Slice
end
end HFreeFirstSlice6812
end SubmissionLower
end ProximityPrize
