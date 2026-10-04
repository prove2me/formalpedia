-- Prove2me | solution 1 for ProximityPrize.SubmissionLower.WholeSpaceCubeUniform6814.exists_root_remainder_uniform_yukon_2354b53a5328
-- status  : ACCEPTED   (prove)
-- author  : @yukon
-- created : 2026-10-02T23:05:09.064342+00:00
-- url     : https://prove2.me/submissions/5ac9752b-7a82-497a-b65c-8c8d88a4917a

import Definitions.Def_Yukon_ca06e00072579899a61b0098



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
import Theorems.Thm_ProximityPrize_SubmissionLower_WholeSpaceCubeUniform6814_remainder_of_not_cube_yukon_11be1c5b7773
import Definitions.Def_Yukon_3c19b1443a389ff3be7252a3
import Definitions.Def_Yukon_9e6b0bff61d8a97ca7ca80a3
set_option backward.isDefEq.respectTransparency.types false
private abbrev ProximityPrize.SubmissionLower.WholeSpaceCubeUniform6814.remainder_of_not_cube := @ProximityPrize.SubmissionLower.WholeSpaceCubeUniform6814.remainder_of_not_cube_yukon_11be1c5b7773
namespace ProximityPrize.SubmissionLower.WholeSpaceCube6814
end WholeSpaceCube6814
end SubmissionLower
end ProximityPrize
namespace MvPolynomial
end MvPolynomial
namespace ProximityPrize.SubmissionLower.WholeSpaceCubeUniform6814
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
open scoped BigOperators
open MvPolynomial WholeSpaceCube6814
variable {K : Type*} [Field K]
/-- Whole-space avoidance followed by the exact field-root handoff.
The output cofactor remains a curvature relation and no longer contains
J. In the application J is primitive irreducible, so this is the proper
pair needed by the new count; clearing/geometry is not assumed here. -/
theorem _root_.solution
    {E : Type*} [Field E]
    (V : Submodule K (Poly (K := K))) [Module.Finite K V]
    (hdim : 627003341034 ≤ Module.finrank K V)
    (hcode : ∀ P ∈ V, weightedTotalDegree codeWeights P < 13050360)
    (htotal : ∀ P ∈ V, weightedTotalDegree totalWeights P ≤ 1700)
    (hmiddle : ∀ P ∈ V, weightedTotalDegree middleWeights P ≤ 98)
    (hslope : ∀ P ∈ V, weightedTotalDegree slopeWeights P ≤ 31)
    (hsdegree : ∀ P ∈ V, P.degreeOf 1 ≤ 14)
    (J : Poly (K := K)) (hJ : J≠0)
    (hm : 25 ≤ weightedTotalDegree middleWeights J)
    (hb : weightedTotalDegree slopeWeights J=9)
    (phi : Poly (K := K) →+* Polynomial E) (sigma : E)
    (hphi : phi J ≠ 0) (hroot : (phi J).rootMultiplicity sigma=1)
    (hret : ∀ P ∈ V, (Polynomial.X-Polynomial.C sigma)^3 ∣ phi P) :
    ∃ P ∈ V, P≠0 ∧ ∃ e < 3, ∃ Q : Poly (K := K),
      P=J^e*Q ∧ ¬ J ∣ Q ∧ (phi Q).eval sigma=0 ∧
      weightedTotalDegree totalWeights Q ≤ 1700 ∧
      weightedTotalDegree middleWeights Q ≤ 98 ∧
      weightedTotalDegree slopeWeights Q ≤ 31 ∧ Q.degreeOf 1 ≤ 14  := by
  obtain ⟨P,hP,hnot⟩ := exists_not_dvd_cube_uniform V hdim hcode htotal hmiddle hslope J hJ hm hb
  have hP0 : P≠0 := by
    intro hz
    exact hnot (by rw [hz]; exact dvd_zero _)
  obtain ⟨e,he,Q,hPQ,hJQ⟩ := remainder_of_not_cube J P hnot
  have hQ0 : Q≠0 := by intro hz; exact hJQ (by rw [hz]; exact dvd_zero _)
  have hrootQ : (phi Q).eval sigma=0 := by
    by_contra hval
    have hpower := hret P hP
    rw [hPQ,map_mul,map_pow] at hpower
    have hh := UniqueCurvatureOwner6814.simple_unique_owner_exponent
      (phi J) (phi Q) sigma 3 e hphi hval hroot hpower
    omega
  have hw (w : Fin 5 → ℕ) (C : ℕ) (hc : weightedTotalDegree w P ≤ C) :
      weightedTotalDegree w Q ≤ C := by
    rw [hPQ,weight_mul w _ _ (pow_ne_zero _ hJ) hQ0] at hc
    omega
  have hd := hsdegree P hP
  rw [hPQ,MvPolynomial.degreeOf_mul_eq (pow_ne_zero _ hJ) hQ0] at hd
  exact ⟨P,hP,hP0,e,he,Q,hPQ,hJQ,hrootQ,
    hw _ _ (htotal P hP),hw _ _ (hmiddle P hP),hw _ _ (hslope P hP),by omega⟩
end
end WholeSpaceCubeUniform6814
end SubmissionLower
end ProximityPrize
