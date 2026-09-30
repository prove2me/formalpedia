-- Prove2me | solution 1 for TauCeti.EulerProductData.restrictAway_apply
-- status  : ACCEPTED   (prove)
-- author  : @riccardo.brasca
-- created : 2026-09-29T21:17:02.389085+00:00
-- url     : https://prove2.me/submissions/d4d21ce0-8143-4686-9c95-5d7140004a3c

/- Transplanted from https://github.com/TauCetiProject/TauCeti at 948fe4751b1fe528b6d580c522ca5d743d47f185.
Original source copyright/license notices are retained below.
Generated exclusively from compiler declaration, command, and reference facts. -/
import Definitions.Def_TauCeti_NumberTheory_ArithmeticDirichletSeries_Basic
import Definitions.Def_TauCeti_NumberTheory_ArithmeticDirichletSeries_EulerProduct_Basic
import Definitions.Def_TauCeti_NumberTheory_ArithmeticDirichletSeries_EulerProduct_Data
import Definitions.Def_TauCeti_RingTheory_DedekindDomain_Ideal
import Mathlib.Algebra.Algebra.Subalgebra.Basic
import Mathlib.Algebra.CharZero.Infinite
import Mathlib.Algebra.Ring.Subgroup
import Mathlib.Algebra.Ring.Subring.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Order
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Complex.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.ZMod.Units
import Mathlib.LinearAlgebra.Pi
import Mathlib.NumberTheory.ArithmeticFunction.Defs
import Mathlib.NumberTheory.ArithmeticFunction.LFunction
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
import Mathlib.RingTheory.DedekindDomain.Factorization
import Mathlib.RingTheory.DedekindDomain.Ideal.Basic
import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.RingTheory.Ideal.Norm.AbsNorm
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.RingTheory.Ideal.Quotient.HasFiniteQuotients
import Mathlib.RingTheory.UniqueFactorizationDomain.Finite
import Mathlib.RingTheory.Valuation.Discrete.IsDiscreteValuationRing
import Mathlib.Tactic.Ring

section
set_option autoImplicit true
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
/-!
# Euler-product coefficient data over a number field

This file bundles the algebraic input for an Euler product over the height-one primes of the ring
of integers of a number field. An `EulerProductData K` consists of an ideal arithmetic function
that is multiplicative on relatively prime nonzero ideals. The prime-power series and local
arithmetic factors are canonically derived from the function as defined in
`EulerProduct/Basic.lean`, so nothing about the local behaviour is stored: the bundle carries
exactly the one algebraic hypothesis that an Euler product consumes.

The formal Euler-product identity follows from
`IdealArithmeticFunction.normCoeff_eq_eulerProduct`: coprime multiplicativity and unique
factorization prove that `normCoeff` is Mathlib's `ArithmeticFunction.eulerProduct` of the
canonical local factors.

Two hypotheses of the classical theory are deliberately absent, because the identity proved here
does not need either. There is no distinguished finite set of exceptional primes: multiplicativity
is required on every coprime pair of nonzero ideals, and the local factor at a prime is read off
from the coefficients at its powers, good or bad. There is also no analytic input: the identity is
an equality of arithmetic functions, and the convergence of the evaluated factors to an infinite
product is a separate question.

## Main definitions

* `TauCeti.EulerProductData` bundles a multiplicative ideal coefficient system.
* `TauCeti.EulerProductData.ofMultiplicativeIdealWeight` regards a degree-one ideal weight as
  Euler-product data.
* Pointwise multiplication, complex conjugation, and restriction away from sets of primes
  preserve the bundle.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter VII.
* Mathlib's `ArithmeticFunction.ofPowerSeries` and `ArithmeticFunction.eulerProduct` APIs.
-/

 section

namespace TauCeti
end TauCeti
section TauCeti
open TauCeti

open scoped _root_.nonZeroDivisors _root_.NumberField
open _root_.IsDedekindDomain (HeightOneSpectrum)



namespace TauCeti.EulerProductData
end TauCeti.EulerProductData
section EulerProductData
open TauCeti TauCeti.EulerProductData

variable {K : Type*} [Field K] [NumberField K]















































open scoped Classical in

theorem solution (D : _root_.TauCeti.EulerProductData K) (S : _root_.Set (_root_.IsDedekindDomain.HeightOneSpectrum (𝓞 K)))
    (I : (_root_.Ideal (𝓞 K))⁰) :
    D.restrictAway S I = if _root_.Ideal.IsPrimeTo (I : _root_.Ideal (𝓞 K)) S then D I else 0 := by
  classical
  -- The bundle's `CoeFun` coercion is the `toIdealArithmeticFunction` projection, so the goal is
  -- definitionally a statement about `IdealArithmeticFunction.supportedPart`. No simp lemma
  -- exposes that projection through `restrictAway`, so reduce to it once here and then argue
  -- entirely through the `supportedPart` interface.
  change _root_.TauCeti.IdealArithmeticFunction.supportedPart D.toIdealArithmeticFunction Sᶜ I = _
  by_cases hI : _root_.Ideal.IsPrimeTo (I : _root_.Ideal (𝓞 K)) S
  · have hI' : _root_.Ideal.IsPrimeTo (I : _root_.Ideal (𝓞 K)) (Sᶜ)ᶜ := by
      simpa only [_root_.compl_compl] using hI
    simpa only [hI, ↓_root_.reduceIte] using
      (_root_.TauCeti.IdealArithmeticFunction.supportedPart_apply_of_isPrimeTo_compl
        (f := D.toIdealArithmeticFunction) (S := Sᶜ) (A := I) hI')
  · have hI' : ¬ _root_.Ideal.IsPrimeTo (I : _root_.Ideal (𝓞 K)) (Sᶜ)ᶜ := by
      simpa only [_root_.compl_compl] using hI
    simpa only [hI, ↓_root_.reduceIte] using
      (_root_.TauCeti.IdealArithmeticFunction.supportedPart_apply_of_not_isPrimeTo_compl
        (f := D.toIdealArithmeticFunction) (S := Sᶜ) (A := I) hI')

end EulerProductData

end TauCeti

end
end
