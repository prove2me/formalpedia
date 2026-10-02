-- Prove2me | solution 1 for ProximityPrize.SubmissionLower.HFree6812.nu_place_bound_yukon_c7b74719de00
-- status  : ACCEPTED   (prove)
-- author  : @yukon
-- created : 2026-10-02T06:36:04.602227+00:00
-- url     : https://prove2.me/submissions/22208648-9d26-4536-a05b-628eb79a5405

import Definitions.Def_Yukon_867f9fe91b5fcd4219c71561

import Definitions.Def_Yukon_40ebcc12c6d7b8bd9832993d

import Definitions.Def_Yukon_c5a0e39377dc346e7a8ed2ec

import Mathlib.RingTheory.Nullstellensatz
import Mathlib.RingTheory.KrullDimension.Polynomial


import Mathlib.Algebra.Order.GroupWithZero.Canonical
import Mathlib.RingTheory.Valuation.Basic
import Init
import Mathlib.Tactic.LinearCombination
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.RingTheory.Derivation.Basic
import Mathlib.FieldTheory.Separable
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.Algebra.Field.Subfield.Basic
import Mathlib.Algebra.Polynomial.Lifts
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.RingTheory.Valuation.ValuationSubring
import Mathlib.RingTheory.AlgebraicIndependent.Transcendental
import Mathlib.RingTheory.Polynomial.Resultant.Basic
import Mathlib.RingTheory.Polynomial.UniqueFactorization
import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.Algebra.MvPolynomial.Monad
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.Data.Nat.Log
import Init.Data.Vector.OfFn
import Mathlib.Algebra.Order.Star.Basic
import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Tactic.Cases
import Mathlib.Order.Lattice.Nat
import Mathlib.Data.List.GetD
import Mathlib.Algebra.GroupWithZero.Nat
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.Algebra.Tropical.Basic
import Mathlib.Tactic.Linarith
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Algebra.Field.TransferInstance
import Mathlib.Tactic.Ring
import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Nat.ModEq
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
import Mathlib.Algebra.Order.Sub.Basic
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Algebra.Polynomial.BigOperators
import Aesop
import Mathlib.Algebra.Polynomial.Bivariate
import Mathlib.Algebra.Ring.TransferInstance
import Mathlib.Algebra.Polynomial.Inductions
import Mathlib.Algebra.Polynomial.OfFn
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
import Definitions.Def_Yukon_88acd699d7b2611ef3b71a58
import Definitions.Def_Yukon_5a1990f0b7b832b98b8bcadb
import Definitions.Def_Yukon_8a240e81f8649dccddb88225
import Definitions.Def_Yukon_a9a7f17ede75ca0ceb0597e1
import Definitions.Def_Yukon_196ff1de7425c8d8df8d3a11
import Definitions.Def_Yukon_07bb1fdf83fc478e7c5449e7
import Definitions.Def_Yukon_755f5ab5e1dfa660f8e11f09
import Definitions.Def_Yukon_19e49f429e40ab4a8ab6f6e7
set_option backward.isDefEq.respectTransparency.types false
namespace ProximityPrize.SubmissionLower.RCN204
end RCN204
end SubmissionLower
end ProximityPrize
namespace ProximityPrize.SubmissionLower.RCN095
end RCN095
end SubmissionLower
end ProximityPrize
namespace ProximityPrize.SubmissionLower.RCN055
end RCN055
end SubmissionLower
end ProximityPrize
namespace ProximityPrize.SubmissionLower.RCN313
end RCN313
end SubmissionLower
end ProximityPrize
namespace ProximityPrize.SubmissionLower.RCN341
end RCN341
end SubmissionLower
end ProximityPrize
namespace ProximityPrize.SubmissionLower.RCN219
end RCN219
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
namespace ProximityPrize.SubmissionLower.RCN202
end RCN202
end SubmissionLower
end ProximityPrize
namespace ProximityPrize.SubmissionLower.RCN208
end RCN208
end SubmissionLower
end ProximityPrize
namespace ProximityPrize.SubmissionLower.RCN002
end RCN002
end SubmissionLower
end ProximityPrize
namespace MvPolynomial
end MvPolynomial
namespace WithZero
end WithZero
namespace ProximityPrize.SubmissionLower.HFree6812
open WithZero MvPolynomial
open RCN002 RCN208 RCN202 RCN135 RCN136 RCN219 RCN341 RCN313 RCN055 RCN095 RCN204
section Budget
variable {K : Type} [Field K] {E : Type} [Field E] [IsAlgClosed E]
  [Algebra (GenericField K) E] [Algebra (RatFunc (GenericField K)) E]
  [IsScalarTower (GenericField K) (RatFunc (GenericField K)) E]
local notation "w" => RCN326.w
/-- **Per-place bound at a slice place**, in the consumer's quantities. -/
theorem _root_.solution (F : MvPolynomial (Fin 4) K) (D : Ideal (MvPolynomial (Fin 3) E))
    [D.IsPrime] (F₀ : MvPolynomial (Fin 4) K) [Fact (Irreducible F₀)] (hdvd : F₀ ∣ F)
    (hker : RingHom.ker (sliceMap (K := K) D) = Ideal.span {F₀})
    (hHD : surfaceMap (phiE K E) (polyH K F) ∉ D)
    (c : Fin 3 → GenericField K) (q : Fin 3 → Polynomial K)
    (hq : ∀ m, polynomialEmbedding K (q m) = c m)
    (hslice : MvPolynomial.C (sliceValue (GenericField K) E) -
      scalarPolynomialMap (GenericField K) E
        (∑ m, MvPolynomial.C (c m) * MvPolynomial.X m) ∈ D)
    (h2 : (2 : K) ≠ 0)
    (ν : RCN026.Place E (CoordinateField E D))
    (hchar : ∀ n : ℕ, 0 < n → (n : ℤ) ≤ max (flagPole ν.val (coordinate E D) unitAllFlag)
      (RCN026.zeroOrder E (CoordinateField E D) ν
        (SecondJetComponentRoots.coefficientMap (phiE K E) D (polyH K F))) → (n : K) ≠ 0)
    (hdefer : ∀ (e : ℕ) (v : Valuation (SliceField F₀) ℤᵐ⁰), 1 ≤ e → (∃ x, v x = exp (-1)) →
      (∀ x, ν.val (sliceEmbedding D F₀ hker x) = v x ^ e) →
      (∃ C, CrudeBound v (sliceDerivation F F₀ hdvd) C) ∧
      ResiduallySeparable v (sliceDerivation F F₀ hdvd)
        (exp (vpole v (sliceDerivation F F₀ hdvd (sliceLinearL F₀ q))))) :
    3 * RCN187.poleOrder ν.val
      (SecondJetComponentRoots.coefficientMap (phiE K E) D (baseNumerator F (w-1)) /
        SecondJetComponentRoots.coefficientMap (phiE K E) D (polyH K F)^(2*w-1)) ≤
    ((w+1 : ℕ) : ℤ) *
      (4*RCN064.movingPoleTarget D (surfaceMap (phiE K E) (polyH K F))
          (surfaceMap (phiE K E) (polyG K F)) ν +
        2*RCN026.zeroOrder E (CoordinateField E D) ν
          (SecondJetComponentRoots.coefficientMap (phiE K E) D (polyH K F))) +
      3*flagPole ν.val (coordinate E D) unitAllFlag  := by
  classical
  set ψ := sliceEmbedding D F₀ hker with hψdef
  set Dd := sliceDerivation F F₀ hdvd with hDd
  set wv : Valuation (SliceField F₀) ℤᵐ⁰ := ν.val.comap ψ with hwvdef
  have hwv : ∀ x, wv x = ν.val (ψ x) := fun _ => rfl
  have hHψ : ψ (sliceProj F₀ (polyH K F)) ≠ 0 := by
    rw [hψdef, sliceEmbedding_proj]
    intro h
    exact hHD ((coordEval_eq_zero_iff D _).1 h)
  have hH : sliceProj F₀ (polyH K F) ≠ 0 := fun h => hHψ (by rw [h, map_zero])
  have hτ : SecondJetComponentRoots.coefficientMap (phiE K E) D (baseNumerator F (w-1)) /
      SecondJetComponentRoots.coefficientMap (phiE K E) D (polyH K F)^(2*w-1) =
      ψ ((⇑Dd)^[w] (sliceCoord F₀ 1)) := by
    have h := sliceDerivation_iterate F F₀ hdvd hH (w - 1)
    have hw1 : w - 1 + 1 = w := rfl
    have hw2 : 2 * (w - 1) + 1 = 2 * w - 1 := rfl
    rw [hw1, hw2] at h
    rw [show sliceCoord F₀ 1 = sliceProj F₀ (MvPolynomial.X 2) from rfl, h, map_div₀, map_pow,
      hψdef, sliceEmbedding_proj, sliceEmbedding_proj]
    rfl
  rw [hτ]
  have hRHS0 : 0 ≤ ((w+1 : ℕ) : ℤ) *
      (4*RCN064.movingPoleTarget D (surfaceMap (phiE K E) (polyH K F))
          (surfaceMap (phiE K E) (polyG K F)) ν +
        2*RCN026.zeroOrder E (CoordinateField E D) ν
          (SecondJetComponentRoots.coefficientMap (phiE K E) D (polyH K F))) +
      3*flagPole ν.val (coordinate E D) unitAllFlag := by
    have h1 : 0 ≤ RCN064.movingPoleTarget D (surfaceMap (phiE K E) (polyH K F))
        (surfaceMap (phiE K E) (polyG K F)) ν := by
      unfold RCN064.movingPoleTarget
      exact le_max_of_le_left (mul_nonneg (by norm_num)
        (le_max_of_le_left (le_max_left _ _)))
    have h2 := RCN026.zeroOrder_nonneg E (CoordinateField E D) ν
      (SecondJetComponentRoots.coefficientMap (phiE K E) D (polyH K F))
    have h3 := flagPole_nonneg ν.val (coordinate E D) unitAllFlag
    positivity
  by_cases hnt : ∃ x, wv x ≠ 0 ∧ wv x ≠ 1
  swap
  · have hpole : RCN187.poleOrder ν.val (ψ ((⇑Dd)^[w] (sliceCoord F₀ 1))) = 0 := by
      set x := (⇑Dd)^[w] (sliceCoord F₀ 1)
      have hx : wv x = 0 ∨ wv x = 1 := by
        by_contra h; rw [not_or] at h; exact hnt ⟨x, h.1, h.2⟩
      show max 0 (ν.val (ψ x)).log = 0
      rw [← hwv]
      rcases hx with h | h <;> simp [h]
    rw [hpole, mul_zero]
    exact hRHS0
  obtain ⟨e, v, he, hvn, hwve⟩ := exists_normalization wv hnt
  have he0 : e ≠ 0 := by omega
  have hν : ∀ x, ν.val (ψ x) = v x ^ e := fun x => hwve x
  have hpole : ∀ x, RCN187.poleOrder ν.val (ψ x) = e * vpole v x :=
    fun x => poleOrder_pow v wv e hwve x
  have hzeroν : ∀ x, RCN026.zeroOrder E (CoordinateField E D) ν (ψ x) = e * vzero v x :=
    fun x => zeroOrder_pow v wv e hwve x
  have hνE : ∀ a : E, a ≠ 0 → ν.val (algebraMap E (CoordinateField E D) a) = 1 :=
    fun a ha => (ν.property.2).eq_one a ha
  have hφinj : Function.Injective (phiE K E) :=
    (algebraMap (GenericField K) E).injective.comp (polynomialEmbedding_injective K)
  have hK : ∀ a : K, a ≠ 0 → v (algebraMap K (SliceField F₀) a) = 1 := by
    intro a ha
    have h1 : ν.val (ψ (algebraMap K _ a)) = 1 := by
      rw [hψdef, psi_const]
      exact hνE _ (fun h => ha (Polynomial.C_eq_zero.mp (hφinj (h.trans (map_zero _).symm))))
    rw [hν] at h1
    exact le_antisymm ((zm_pow_le_one he0).1 h1.le)
      (not_lt.1 fun hlt => absurd h1 (ne_of_lt ((zm_pow_lt_one he0).2 hlt)))
  have hX0 : v (sliceProj F₀ (MvPolynomial.X 0)) ≤ 1 := by
    have h1 : ν.val (ψ (sliceProj F₀ (MvPolynomial.X 0))) ≤ 1 := by
      rw [hψdef, psi_X0]
      haveI := ν.property.2
      exact Valuation.IsTrivialOn.valuation_algebraMap_le_one ν.val _
    rw [hν] at h1
    exact (zm_pow_le_one he0).1 h1
  obtain ⟨⟨C, hcrude⟩, hsep⟩ := hdefer e v he hvn hwve
  have hℓ := sliceLinearL_bound F F₀ hdvd v hH hK hX0 q
  -- the consumer quantities scale by `e`
  have hcoordν : ∀ j, RCN187.poleOrder ν.val (coordinate E D j) =
      e * vpole v (sliceCoord F₀ j) := by
    intro j; rw [← psi_coord D F₀ hker j, ← hψdef, hpole]
  have hPν : flagPole ν.val (coordinate E D) unitAllFlag = e * placeP F₀ v := by
    simp only [flagPole, unitAllFlag, Nat.cast_zero, zero_mul, Nat.cast_one, one_mul, zero_add]
    rw [hcoordν, hcoordν, hcoordν, placeP, scale_flag (e : ℤ) (by positivity)]
  have hhν : RCN026.zeroOrder E (CoordinateField E D) ν
      (SecondJetComponentRoots.coefficientMap (phiE K E) D (polyH K F)) =
        e * placeH F F₀ v := by
    have : SecondJetComponentRoots.coefficientMap (phiE K E) D (polyH K F) =
        ψ (sliceProj F₀ (polyH K F)) := by rw [hψdef, sliceEmbedding_proj]; rfl
    rw [this, hzeroν]
    rfl
  have hTν : RCN064.movingPoleTarget D (surfaceMap (phiE K E) (polyH K F))
      (surfaceMap (phiE K E) (polyG K F)) ν = e * placeT F F₀ v := by
    unfold RCN064.movingPoleTarget
    rw [hcoordν, hcoordν, hcoordν, ← psi_sigma D F₀ hker F, ← hψdef, hpole, placeT, placeP,
      scale_target (e : ℤ) (by positivity)]
  have hPv0 : 0 ≤ placeP F₀ v := le_max_of_le_left (vpole_nonneg _ _)
  have hhv0 : 0 ≤ placeH F F₀ v := vzero_nonneg _ _
  have hcharv : ∀ n : ℕ, 0 < n → (n : ℤ) ≤ max (placeP F₀ v) (placeH F F₀ v) → (n : K) ≠ 0 := by
    intro n hn hle
    refine hchar n hn ?_
    rw [hPν, hhν]
    have h1 : placeP F₀ v ≤ e * placeP F₀ v := le_mul_of_one_le_left hPv0 (by exact_mod_cast he)
    have h2 : placeH F F₀ v ≤ e * placeH F F₀ v := le_mul_of_one_le_left hhv0 (by exact_mod_cast he)
    exact hle.trans (max_le_max h1 h2)
  have hgen : placeP F₀ v = 0 → ∃ a b : MvPolynomial (Fin 4) K,
      v (sliceProj F₀ a) < 1 ∧ v (sliceProj F₀ b) < 1 ∧
      ∀ g, v (sliceProj F₀ g) < 1 → ∃ s x y : MvPolynomial (Fin 4) K,
        v (sliceProj F₀ s) = 1 ∧ s * g = x * a + y * b := by
    intro hP0
    have hint := place_hint F₀ v hK hX0 hP0
    set 𝔓 := valCentre (sliceProj F₀) v hint with h𝔓def
    set y : Fin 3 → CoordinateField E D := coordinate E D
    have hev : ∀ P : MvPolynomial (Fin 3) (GenericField K),
        aeval y P = coordinateEvaluation E D (scalarPolynomialMap (GenericField K) E P) := by
      intro P
      rw [coordinateEvaluation_eq_aeval, scalarPolynomialMap, aeval_map_algebraMap]
    have hνΩ : ∀ a : GenericField K,
        ν.val (algebraMap (GenericField K) (CoordinateField E D) a) ≤ 1 := by
      intro a
      rw [IsScalarTower.algebraMap_apply (GenericField K) E (CoordinateField E D)]
      haveI := ν.property.2
      exact Valuation.IsTrivialOn.valuation_algebraMap_le_one ν.val _
    have hyint : ∀ j, ν.val (y j) ≤ 1 := by
      intro j
      rw [show y j = ψ (sliceCoord F₀ j) from (psi_coord D F₀ hker j).symm, hν]
      exact pow_le_one' (hint _) e
    let fy : MvPolynomial (Fin 3) (GenericField K) →+* CoordinateField E D := (aeval y).toRingHom
    have hintΩ : ∀ P : MvPolynomial (Fin 3) (GenericField K), ν.val (fy P) ≤ 1 := by
      intro P
      change ν.val (aeval y P) ≤ 1
      induction P using MvPolynomial.induction_on with
      | C a => rw [aeval_C]; exact hνΩ a
      | add p r hp hr => rw [map_add]; exact (ν.val.map_add _ _).trans (max_le hp hr)
      | mul_X p j hp =>
        rw [map_mul, ν.val.map_mul, aeval_X]; exact mul_le_one' hp (hyint j)
    set 𝔮 := valCentre fy ν.val hintΩ with h𝔮def
    have hP𝔮 : originalPrime 𝔮 = 𝔓 := by
      ext g
      rw [mem_originalPrime_iff, h𝔮def, h𝔓def, mem_valCentre, mem_valCentre]
      change ν.val (aeval y _) < 1 ↔ _
      rw [hev, ← surfaceMap_generic_eq]
      change ν.val (sliceMap D g) < 1 ↔ _
      rw [← sliceEmbedding_proj D F₀ hker, ← hψdef, hν, zm_pow_lt_one he0]
    have hcω : ∀ a : GenericField K, a ≠ 0 →
        ν.val (algebraMap (GenericField K) (CoordinateField E D) a) = 1 := by
      intro a ha
      rw [IsScalarTower.algebraMap_apply (GenericField K) E (CoordinateField E D)]
      exact hνE _ ((map_ne_zero_iff _ (algebraMap (GenericField K) E).injective).2 ha)
    have hsl : ∑ m, algebraMap (GenericField K) (CoordinateField E D) (c m) * y m =
        algebraMap E (CoordinateField E D) (sliceValue (GenericField K) E) := by
      have h1 := (coordEval_eq_zero_iff D _).2 hslice
      rw [map_sub, sub_eq_zero, ← hev] at h1
      have h2 : coordinateEvaluation E D (MvPolynomial.C (sliceValue (GenericField K) E)) =
          algebraMap E (CoordinateField E D) (sliceValue (GenericField K) E) :=
        (coordinateEvaluation E D).commutes _
      rw [h2] at h1
      rw [h1]
      simp only [map_sum, map_mul, aeval_C, aeval_X]
    have hℓ' : ∀ a : Fin 3 → GenericField K,
        ν.val (∑ m, algebraMap (GenericField K) (CoordinateField E D) (c m) * y m -
          algebraMap (GenericField K) (CoordinateField E D) (∑ m, c m * a m)) = 1 := by
      intro a
      rw [hsl, IsScalarTower.algebraMap_apply (GenericField K) E (CoordinateField E D),
        ← map_sub]
      apply hνE
      intro h
      apply sliceValue_transcendental (Ω := GenericField K) (E := E)
      rw [sub_eq_zero] at h
      rw [h]
      exact isAlgebraic_algebraMap _
    have h𝔮h : 𝔮.height ≤ 2 :=
      centre_height_le_two ν.val y 𝔮 (fun P => mem_valCentre _ _ _ P) c hcω hℓ'
    have h𝔓h : 𝔓.height ≤ 2 := hP𝔮 ▸ (originalPrime_height_le 𝔮).trans h𝔮h
    haveI := RCN230.mvPolynomial_atPrime_isRegularLocalRing 𝔓
    obtain ⟨a, ha, b, hb, hgen'⟩ := exists_two_local_generators 𝔓 h𝔓h
    refine ⟨a, b, ha, hb, fun g hg => ?_⟩
    obtain ⟨s, hs, x, y, hsg⟩ := hgen' g hg
    exact ⟨s, x, y, le_antisymm (hint s) (not_lt.1 hs), hsg⟩
  have hmain := place_bound F F₀ hdvd v hH hvn hK hX0 (sliceLinearL F₀ q) hℓ C hcrude hsep h2
    hcharv hgen w
  rw [hpole, hTν, hhν, hPν]
  have hT0 : 0 ≤ placeT F F₀ v := le_max_of_le_left (by omega)
  have hvp0 := vpole_nonneg v ((⇑Dd)^[w] (sliceCoord F₀ 1))
  have he1 : (1 : ℤ) ≤ e := by exact_mod_cast he
  have hk := mul_le_mul_of_nonneg_left hmain (show (0 : ℤ) ≤ e by positivity)
  have hprod := mul_nonneg (show (0:ℤ) ≤ e by positivity)
    (show (0:ℤ) ≤ 4 * placeT F F₀ v + 2 * placeH F F₀ v by omega)
  push_cast at hk ⊢
  linarith
end Budget
end HFree6812
end SubmissionLower
end ProximityPrize
