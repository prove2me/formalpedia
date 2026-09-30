-- Prove2me | solution 1 for TauCeti.EulerProductData.LSeriesSummable_normCoeff_supportedPart
-- status  : ACCEPTED   (prove)
-- author  : @riccardo.brasca
-- created : 2026-09-29T21:26:27.204842+00:00
-- url     : https://prove2.me/submissions/45227f73-f811-4319-a4d9-4477d3735f3d

/- Transplanted from https://github.com/TauCetiProject/TauCeti at 948fe4751b1fe528b6d580c522ca5d743d47f185.
Original source copyright/license notices are retained below.
Generated exclusively from compiler declaration, command, and reference facts. -/
import Definitions.Def_TauCeti_NumberTheory_ArithmeticDirichletSeries_Basic
import Definitions.Def_TauCeti_NumberTheory_ArithmeticDirichletSeries_Convolution
import Definitions.Def_TauCeti_NumberTheory_ArithmeticDirichletSeries_EulerProduct_Basic
import Definitions.Def_TauCeti_NumberTheory_ArithmeticDirichletSeries_EulerProduct_Data
import Definitions.Def_TauCeti_NumberTheory_ArithmeticDirichletSeries_NormCoeff
import Definitions.Def_TauCeti_NumberTheory_ArithmeticDirichletSeries_Weight
import Definitions.Def_TauCeti_RingTheory_DedekindDomain_Ideal
import Mathlib.Algebra.Algebra.Subalgebra.Basic
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.CharZero.Infinite
import Mathlib.Algebra.IsPrimePow
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Ring.Subgroup
import Mathlib.Algebra.Ring.Subring.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Order
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Set.Card
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.ZMod.Units
import Mathlib.LinearAlgebra.Pi
import Mathlib.NumberTheory.ArithmeticFunction.Defs
import Mathlib.NumberTheory.ArithmeticFunction.LFunction
import Mathlib.NumberTheory.LSeries.Convergence
import Mathlib.NumberTheory.LSeries.Convolution
import Mathlib.NumberTheory.LSeries.SumCoeff
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
import Mathlib.NumberTheory.NumberField.DedekindZeta
import Mathlib.NumberTheory.NumberField.Ideal.Asymptotics
import Mathlib.NumberTheory.Padics.HeightOneSpectrum
import Mathlib.Order.Filter.AtTopBot.Finset
import Mathlib.Order.Northcott
import Mathlib.RingTheory.DedekindDomain.Factorization
import Mathlib.RingTheory.DedekindDomain.Ideal.Basic
import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.RingTheory.Ideal.Norm.AbsNorm
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.RingTheory.Ideal.Quotient.HasFiniteQuotients
import Mathlib.RingTheory.UniqueFactorizationDomain.Finite
import Mathlib.RingTheory.Valuation.Discrete.IsDiscreteValuationRing
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Topology.Algebra.Order.Floor
import Mathlib.Topology.UniformSpace.Real
import Theorems.Thm_TauCeti_IdealArithmeticFunction_normCoeff_supportedPart_singleton
import Theorems.Thm_TauCeti_IdealArithmeticFunction_supportedPart_insert
import Theorems.Thm_TauCeti_normCoeff_convolution
import Theorems.Thm_TauCeti_normCoeff_delta

section
set_option autoImplicit true
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
/-!
# Complements on ideals of a Dedekind domain

This file collects general facts about ideals and height-one primes of a Dedekind domain,
complementing `Mathlib/RingTheory/DedekindDomain/Ideal/Lemmas.lean`. In particular, it develops
the predicate `Ideal.IsPrimeTo I S`, saying that `I` is nonzero and divisible by no prime in `S`,
together with its induction principle `Ideal.IsPrimeTo.induction_on` and its transport
`Ideal.isPrimeTo_comap_iff` along a ring isomorphism.

The predicate is closed under products (`Ideal.isPrimeTo_mul_iff`, its finite form
`Ideal.isPrimeTo_prod_iff`) and powers (`Ideal.isPrimeTo_pow_iff`), and forbidding one more
prime is `Ideal.isPrimeTo_insert_iff`. Complementing a set of primes
turns it into a *support* condition: `IsPrimeTo I Sᶜ` says that every prime factor of `I` lies in
`S`. The two extreme cases are `Ideal.isPrimeTo_univ_iff` (no prime factor at all, so `I = ⊤`) and
`Ideal.isPrimeTo_compl_singleton_iff` (a single allowed prime, so `I` is a prime power), and
`Ideal.IsPrimeTo.exists_eq_pow_mul` splits off one allowed prime at a time. The file also records
the prime-power factorization `Ideal.exists_eq_prod_pow` of an arbitrary nonzero ideal. Together
with the uniqueness statement `Ideal.eq_and_eq_of_pow_mul_eq_pow_mul` and the relative primality
`Ideal.IsPrimeTo.isRelPrime` of ideals supported on complementary sets, these are what turn a
finite set of primes into a finite Euler product in
`TauCeti/NumberTheory/ArithmeticDirichletSeries/EulerProduct/Basic.lean`.

It also collects how an isomorphism `e : R ≃+* R'` moves ideals: `Ideal.map e` preserves
divisibility (`Ideal.map_dvd_map_iff_of_ringEquiv`, `Ideal.map_pow_dvd_map_iff_of_ringEquiv`,
stated over commutative *semirings*, since the proofs use only that `Ideal.map e` and
`Ideal.map e.symm` are mutually inverse) and factorisation multiplicities
(`Ideal.count_factors_map_of_ringEquiv`), and Mathlib's transport `equivOfRingEquiv e` of height
one primes is `Ideal.map e` on underlying ideals
(`IsDedekindDomain.HeightOneSpectrum.asIdeal_equivOfRingEquiv`). Those four are the ideal-level
input to the adic-valuation transport in
`TauCeti/RingTheory/DedekindDomain/AdicValuation/Transport.lean`; they are adapted from
[AINTLIB](https://github.com/CBirkbeck/AINTLIB) (Apache-2.0), commit `513e83879e2f`,
`projects/HasseWeil/HasseWeil/WeilPairing/DivisorGalois.lean`.

`Ideal.IsPrimeTo` generalizes the `IsGood` predicate of
`TauCetiRoadmap/ArithmeticDirichletSeries/Suggested.lean`, where it is stated for the bad primes
of an ideal weight on a number field; the design of the predicate — nonzeroness included, so that
`⊥` is prime to no set at all — is taken from there, while nothing in it is specific to a number
field.

The file also identifies any height-one prime of a discrete valuation ring with its maximal ideal
(`IsDedekindDomain.HeightOneSpectrum.eq_maximalIdeal`), which is what lets a condition stated at
the height-one primes of such a ring be read as a condition on its valuation. It was split out of
material adapted from Michael Stoll's elliptic-curves formalisation
(`EllipticCurves/Mathlib/AdicCompletionExtension.lean` at the roadmap's pin `66889eada51a`,
Apache 2.0, by Michael Stoll), where it is the step behind `valuation_adicCompletion_algebraMap`.

The theorem `IsDedekindDomain.HeightOneSpectrum.exists_mem_notMem` was split out of material
adapted from Michael Stoll's elliptic-curves formalisation
(`github.com/MichaelStollBayreuth/EllipticCurves`, `EllipticCurves/Mathlib/SIntegers.lean` at the
roadmap's pin `66889eada51a`, Apache 2.0, by Michael Stoll); following this repository's
convention for adapted material, the upstream authorship is credited here rather than in the
copyright header.

`IsDedekindDomain.HeightOneSpectrum.comapOfNeBot` and its projection are likewise adapted from that
formalisation (`github.com/MichaelStollBayreuth/EllipticCurves`, `EllipticCurves/Mathlib/Basic.lean`
line 539, at the roadmap's pin `66889eada51a74c2f5dfb7fb5909b0b5a0a2d96e`, Apache 2.0, by Michael
Stoll). The construction is the source's; what changed is the hypothesis — the source and this
version take the nonvanishing of the contraction as a hypothesis, where Mathlib's
`HeightOneSpectrum.comap` instead derives it from surjectivity of the map.

`Ideal.ne_bot_of_comap_ne_bot` plays the role of the source's
`comap_ne_bot_of_comap_comap_ne_bot` (`EllipticCurves/Mathlib/Basic.lean` line 270): it is what
discharges that nonvanishing hypothesis when a prime is contracted through an intermediate ring.
It is stated here in the general form — an arbitrary ideal and an injective ring homomorphism,
with the map producing the ideal dropped, since it plays no role — and proved from Mathlib's
`Ideal.comap_bot_of_injective`.
-/

 section

namespace Ideal

section CommSemiring

variable {R R' : Type*} [CommSemiring R] [CommSemiring R']





end CommSemiring

section RingEquivDedekind

variable {R R' : Type*} [CommRing R] [IsDedekindDomain R] [CommRing R'] [IsDedekindDomain R']



end RingEquivDedekind

section Multiplicity

variable {B : Type*} [CommRing B] [IsDedekindDomain B]



end Multiplicity

section Injective



end Injective

end Ideal

namespace IsDedekindDomain.HeightOneSpectrum

section Comap

variable {B C : Type*} [CommRing B] [IsDedekindDomain B] [CommRing C] [IsDedekindDomain C]





end Comap

section RingEquivTransport

variable {R R' : Type*} [CommRing R] [CommRing R']



end RingEquivTransport

end IsDedekindDomain.HeightOneSpectrum

namespace IsDedekindDomain.HeightOneSpectrum

variable {R : Type*} [CommRing R] [IsDedekindDomain R]



end IsDedekindDomain.HeightOneSpectrum

namespace Ideal

-- `_root_` disambiguates: inside `namespace Ideal`, a bare `open IsDedekindDomain` would resolve
-- to the `Ideal.IsDedekindDomain` namespace of Mathlib's ramification indices, which the
-- `Factorization` import above makes visible here.
open _root_.IsDedekindDomain

variable {R : Type*} [CommRing R] [IsDedekindDomain R]



variable {I J : Ideal R} {S T : Set (HeightOneSpectrum R)}































/-- An ideal divisible by no height-one prime at all is the unit ideal. -/
@[simp]
theorem isPrimeTo_univ_iff : IsPrimeTo I Set.univ ↔ I = ⊤ := by
  refine ⟨fun h ↦ h.induction_on rfl fun 𝔭 _ h𝔭 _ _ ↦ absurd (Set.mem_univ 𝔭) h𝔭, ?_⟩
  rintro rfl
  exact isPrimeTo_top













end Ideal

section DiscreteValuationRing

namespace IsDedekindDomain.HeightOneSpectrum



end IsDedekindDomain.HeightOneSpectrum

end DiscreteValuationRing

end

end

section
set_option autoImplicit true
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
/-!
# Ideal convolution of ideal arithmetic functions

The Dirichlet convolution of two arithmetic functions on the nonzero ideals of the ring of integers
of a number field `K` sums over the factorizations `B * C = A` of a nonzero ideal `A`. This file
constructs that index set, defines the convolution, and proves that it makes
`TauCeti.IdealArithmeticFunction K` a commutative monoid with identity
`TauCeti.IdealArithmeticFunction.delta`, bilinear over the pointwise additive structure.
It also transports this operation through `TauCeti.normCoeff` to Mathlib's Dirichlet convolution
on `ArithmeticFunction ℂ`.

## Main definitions

* `TauCeti.IdealArithmeticFunction.delta` is the ideal arithmetic function that is `1` at the unit
  ideal and `0` elsewhere.
* `TauCeti.Ideal.divisorsAntidiagonal A` is the finite set of pairs `(B, C)` of nonzero ideals with
  `B * C = A`; it is the ideal analogue of Mathlib's `Nat.divisorsAntidiagonal`.
* `TauCeti.IdealArithmeticFunction.convolution f g` is the ideal Dirichlet convolution.
* `TauCeti.IdealArithmeticFunction.convolutionPow f n` is the `n`-fold convolution power of `f`.

## Main results

* `TauCeti.IdealArithmeticFunction.convolution_comm`,
  `TauCeti.IdealArithmeticFunction.convolution_assoc`,
  `TauCeti.IdealArithmeticFunction.delta_convolution` and
  `TauCeti.IdealArithmeticFunction.convolution_delta`: the convolution monoid laws.
* `TauCeti.IdealArithmeticFunction.convolution_add` and
  `TauCeti.IdealArithmeticFunction.add_convolution`: bilinearity over pointwise addition.
* `TauCeti.IdealArithmeticFunction.convolution_one_one_ne_mul`: ideal convolution is not the
  pointwise product.
* `TauCeti.normCoeff_delta`, `TauCeti.normCoeff_convolution`, and
  `TauCeti.normCoeff_convolutionPow`: regrouping by absolute norm transports the convolution
  identity, convolution, and convolution powers to Mathlib arithmetic functions.

## Implementation notes

`TauCeti.IdealArithmeticFunction K` is a `Pi` type, so it already carries Mathlib's *pointwise*
`CommRing` structure, in which `f * g` is `fun A => f A * g A` and `1` is the everywhere-one
function. Convolution is therefore deliberately **not** registered as a `Mul` instance and its
identity is the separate function `TauCeti.IdealArithmeticFunction.delta`; this is the roadmap's
convention that pointwise multiplication and ideal convolution stay distinct operations on one
carrier. The monoid laws are stated as ordinary theorems about
`TauCeti.IdealArithmeticFunction.convolution`, and
`TauCeti.IdealArithmeticFunction.convolution_one_one_ne_mul` records that the two products really do
differ. Consequently iterated convolution is the explicit
`TauCeti.IdealArithmeticFunction.convolutionPow` rather than a `Monoid.npow`.

Excluding the zero ideal from the carrier is what makes the index set finite: `⊥ * J = ⊥` for every
`J`, so the zero ideal has infinitely many factorizations while a nonzero ideal has only finitely
many, by Mathlib's `UniqueFactorizationMonoid.fintypeSubtypeDvd` for the unique factorization
monoid `Ideal (𝓞 K)`.

## Roadmap role

This is Layer **2.1** of `TauCetiRoadmap/ArithmeticDirichletSeries/README.md`, built on the Layer
**0.1** carrier of `TauCeti/NumberTheory/ArithmeticDirichletSeries/Basic.lean`. Its consumers are
the ideal Möbius function and von Mangoldt transform of Layer 2 and the local factors of Layer 3.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter VII.
* G. Tenenbaum, *Introduction to Analytic and Probabilistic Number Theory*, Chapters II--III.
-/

 section

namespace TauCeti

open scoped nonZeroDivisors NumberField

namespace IdealArithmeticFunction

variable {K : Type*} [Field K]

/-! ### The convolution identity -/



/-- The delta function takes the value `1` at the unit ideal. -/
@[simp]
theorem delta_one : delta (1 : (Ideal (𝓞 K))⁰) = 1 := by
  simp [delta]

/-- The delta function vanishes away from the unit ideal. -/
@[simp]
theorem delta_of_ne_one {A : (Ideal (𝓞 K))⁰} (hA : A ≠ 1) : delta A = 0 := by
  simp [delta, hA]



end IdealArithmeticFunction

variable {K : Type*} [Field K] [NumberField K]

namespace Ideal

/-! ### The antidiagonal of a nonzero ideal -/

















end Ideal

namespace IdealArithmeticFunction

/-! ### Ideal convolution -/







/-! ### The monoid laws -/









/-! ### Bilinearity over the pointwise additive structure -/





















/-! ### Iterated convolution -/













/-! ### Convolution is not the pointwise product -/





end IdealArithmeticFunction

/-! ## Compatibility with Dirichlet convolution -/

variable (K : Type*) [Field K] [NumberField K]







end TauCeti

end
end

section
set_option autoImplicit true
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
/-!
# Canonical local factors and formal Euler products for ideal arithmetic functions

This file develops the Euler-product layer for arithmetic functions on nonzero ideals. It builds
the canonical formal power series at each height-one prime and sends that series into Mathlib's
`ArithmeticFunction.ofPowerSeries` API. The resulting local arithmetic factor has the prescribed
prime-power values and vanishes away from powers of the prime-ideal norm.

It then restricts an ideal arithmetic function to the nonzero ideals whose prime factors lie in a
prescribed set of height-one primes, and proves that for a *finite* set of primes the norm
coefficients of that restriction are exactly the product of the local factors, taken in Mathlib's
Dirichlet convolution of arithmetic functions. Passing to Mathlib's formal Euler product gives the
norm coefficients of the original function. Everything here is a formal identity of coefficients:
no analytic convergence hypothesis enters.

## Main definitions

* `TauCeti.IdealArithmeticFunction.localPowerSeries` has coefficient `f (P ^ n)` at `n`.
* `TauCeti.IdealArithmeticFunction.localArithmeticFactor` realizes that power series as an
  arithmetic function supported on powers of `N(P)`.
* `TauCeti.IdealArithmeticFunction.supportedPart f S` is `f` restricted to the nonzero ideals all
  of whose prime factors lie in `S`, and zero elsewhere.

## Main results

* `TauCeti.IdealArithmeticFunction.supportedPart_insert`: for a multiplicative `f`, adjoining one
  prime to the support convolves the restriction with the restriction to the powers of that prime.
* `TauCeti.IdealArithmeticFunction.normCoeff_supportedPart`: the **finite Euler product**
  `normCoeff (supportedPart f S) = ∏ P ∈ S, localArithmeticFactor f P` for a multiplicative `f`
  and a finite set `S` of height-one primes.
* `TauCeti.IdealArithmeticFunction.normCoeff_eq_eulerProduct`: the norm coefficients of a
  multiplicative ideal arithmetic function are Mathlib's formal Euler product of its canonical
  local factors.

## Implementation notes

"Supported on `S`" is spelled `Ideal.IsPrimeTo · Sᶜ`: no prime *outside* `S` divides the ideal.
That predicate, and the splitting `Ideal.IsPrimeTo.exists_eq_pow_mul` of an ideal into a prime
power times a cofactor together with its uniqueness `Ideal.eq_and_eq_of_pow_mul_eq_pow_mul`, live
in `TauCeti/RingTheory/DedekindDomain/Ideal.lean`, since nothing in them is specific to a number
field. Uniqueness is what makes the induction work: it is why exactly one summand of the ideal
convolution survives at each ideal. The multiplicativity of `f` over a prime-power factorization,
`TauCeti.IdealArithmeticFunction.IsMultiplicative.map_prod_pow`, likewise lives with the predicate
it elaborates, in `TauCeti/NumberTheory/ArithmeticDirichletSeries/Basic.lean`.

`TauCeti.MultiplicativeIdealWeight.restrict` is the opposite regime and is not a substitute:
it restricts *away from* a **finite** set of primes and stays inside the bundled weight carrier. A
finite Euler product needs support on a *finite* set of primes, so all but finitely many primes are
bad; such a function is never a `MultiplicativeIdealWeight`, whose zero support is finite by
definition. Hence `supportedPart` is a plain ideal arithmetic function.

Finiteness is what carries the finite products to the full Euler product. A nonzero ideal has
only finitely many prime divisors, and only finitely many primes have norm at most a given `n`, so
at a fixed norm coefficient the restriction `supportedPart f S` already agrees with `f` as soon as
`S` contains those primes. Each finite product is therefore eventually the exact norm coefficient,
and Mathlib's `ArithmeticFunction.eulerProduct`, being the limit of those finite products, computes
the norm coefficients of `f` itself. The local factors are derived from `f` rather than stored, so
this identity holds for any multiplicative `f` with no further data.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter VII.
* Mathlib's `ArithmeticFunction.ofPowerSeries` and `ArithmeticFunction.eulerProduct` APIs.
* `TauCetiRoadmap/ArithmeticDirichletSeries/Suggested.lean`, whose local-factor target signatures
  and naming are adapted here.
-/

 section

open scoped _root_.nonZeroDivisors _root_.NumberField
open _root_.IsDedekindDomain (HeightOneSpectrum)

namespace IsDedekindDomain.HeightOneSpectrum

variable {K : Type*} [Field K]





variable [NumberField K]







end IsDedekindDomain.HeightOneSpectrum

namespace TauCeti



namespace IdealArithmeticFunction

variable {K : Type*} [Field K]

variable [NumberField K]



























/-! ### Finite Euler products -/



variable {f : IdealArithmeticFunction K} {S : Set (HeightOneSpectrum (𝓞 K))}
  {A : (Ideal (𝓞 K))⁰}













/-- Only the unit ideal is supported on no prime at all, so the empty restriction of a function
taking the value `1` there is the convolution identity. -/
theorem supportedPart_empty (hf : f 1 = 1) : supportedPart f ∅ = delta := by
  funext A
  have hiff : Ideal.IsPrimeTo (A : Ideal (𝓞 K)) (∅ : Set (HeightOneSpectrum (𝓞 K)))ᶜ ↔ A = 1 := by
    rw [Set.compl_empty, Ideal.isPrimeTo_univ_iff, ← Ideal.one_eq_top]
    exact ⟨fun h ↦ Subtype.ext h, fun h ↦ congrArg Subtype.val h⟩
  rcases eq_or_ne A 1 with rfl | hA
  · rw [supportedPart_apply_of_isPrimeTo_compl (hiff.mpr rfl), delta_one, hf]
  · rw [supportedPart_apply_of_not_isPrimeTo_compl fun h ↦ hA (hiff.mp h), delta_of_ne_one hA]

















end IdealArithmeticFunction

end TauCeti

end
end

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

open scoped _root_.nonZeroDivisors _root_.NumberField
open _root_.IsDedekindDomain (HeightOneSpectrum)



namespace EulerProductData

variable {K : Type*} [Field K] [NumberField K]















/-- The bundled local arithmetic factor is the canonical factor of its coefficient function. -/
theorem localArithmeticFactor_eq (D : EulerProductData K)
    (P : HeightOneSpectrum (𝓞 K)) :
    D.localArithmeticFactor P = D.toIdealArithmeticFunction.localArithmeticFactor P :=
  (rfl)

































end EulerProductData

end TauCeti

end
end

section
set_option autoImplicit true
namespace TauCeti.IdealArithmeticFunction
end TauCeti.IdealArithmeticFunction
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
/-!
# The analytic Euler product of an ideal arithmetic function

`TauCeti.EulerProductData.normCoeff_eq_eulerProduct` identifies the norm coefficients of bundled
Euler-product data with a formal Euler product, coefficient by coefficient. This file supplies the
analytic statement it does not: where the Dirichlet series indexed by the nonzero ideals converges
absolutely, the infinite product of the local Euler factors converges, in the unrestricted sense
of `HasProd` over the height-one primes, to the `LSeries` of the norm coefficients.

The local factor at a height-one prime `P` is the `LSeries` of the canonical local arithmetic
factor, equivalently the prime-power Dirichlet series `∑' e, f (P ^ e) / N(P ^ e) ^ s`. For a
completely multiplicative weight that series is geometric, and the factor takes the familiar
closed form `(1 - χ(P) N(P) ^ (-s))⁻¹`; specializing to the trivial weight gives the Euler
product of the Dedekind zeta function.

## Main definitions

* `TauCeti.EulerProductData.eulerFactor`: the local Euler factor at a height-one prime.

## Main results

* `TauCeti.EulerProductData.hasProd_eulerFactor`: the **analytic Euler product**, when the
  ideal-indexed Dirichlet series converges absolutely at `s`.
* `TauCeti.EulerProductData.norm_absNorm_cpow_neg_le_radius_localPowerSeries`: a lower bound for
  the convergence radius of a local power series from absolute convergence at a real point.
* `TauCeti.MultiplicativeIdealWeight.hasProd_eulerFactor`: the same product, with the local factors
  in the closed geometric form available for a completely multiplicative weight.
* `TauCeti.MultiplicativeIdealWeight.LSeries_ne_zero_of_summable_idealTerm`: the `L`-series is
  **nonzero** wherever the ideal-indexed series converges absolutely.
* `TauCeti.dedekindZeta_eulerProduct_hasProd`: the **Euler product of the Dedekind zeta
  function**, valid on `Re s > 1`.
* `TauCeti.dedekindZeta_ne_zero_of_one_lt_re`: the Dedekind zeta function is **nonzero** on
  `Re s > 1`.
* `IsDedekindDomain.HeightOneSpectrum.one_lt_norm_absNorm_cpow` and
  `IsDedekindDomain.HeightOneSpectrum.absNorm_cpow_sub_one_ne_zero`: analytic bounds for the
  complex powers of prime-ideal norms on the right half-plane.
* `IsDedekindDomain.HeightOneSpectrum.logDeriv_one_sub_absNorm_cpow_neg`: the logarithmic
  derivative of a deleted Euler factor.

The nonvanishing is pointwise, at each `s` where the ideal-indexed series converges absolutely, and
nothing is claimed off that region. It is not a formality: an unconditionally convergent product of
nonzero factors may still vanish.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter VII.
* Mathlib's `EulerProduct` API, whose `Nat.Primes`-indexed statements this file mirrors for the
  height-one primes of a number field.
-/

 section

open scoped _root_.NumberField
open _root_.IsDedekindDomain (HeightOneSpectrum)

namespace IsDedekindDomain.HeightOneSpectrum
end IsDedekindDomain.HeightOneSpectrum
section IsDedekindDomain.HeightOneSpectrum
open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum

variable {K : Type*} [Field K] [NumberField K]











end IsDedekindDomain.HeightOneSpectrum

namespace TauCeti
end TauCeti
section TauCeti
open TauCeti

open scoped _root_.nonZeroDivisors _root_.ComplexOrder

variable {K : Type*} [Field K] [NumberField K]

namespace TauCeti.EulerProductData
end TauCeti.EulerProductData
section EulerProductData
open TauCeti TauCeti.EulerProductData

open _root_.TauCeti.IdealArithmeticFunction

variable (D : EulerProductData K) {s : ℂ}

/-! ### The local Euler factor -/







end EulerProductData

namespace TauCeti.IdealArithmeticFunction
end TauCeti.IdealArithmeticFunction
section IdealArithmeticFunction
open TauCeti TauCeti.IdealArithmeticFunction

variable {f : IdealArithmeticFunction K} {s : ℂ}

/-! ### Restriction to a set of primes, analytically -/









/-- The norm coefficients of the restriction of `f` to no primes are Mathlib's Kronecker delta. -/
theorem TauCeti.IdealArithmeticFunction.coe_normCoeff_supportedPart_empty (hf : f 1 = 1) :
    ⇑(_root_.TauCeti.normCoeff K (_root_.TauCeti.IdealArithmeticFunction.supportedPart f (∅ : _root_.Set (_root_.IsDedekindDomain.HeightOneSpectrum (𝓞 K))))) = _root_.LSeries.delta := by
  rw [_root_.TauCeti.IdealArithmeticFunction.supportedPart_empty hf, _root_.TauCeti.normCoeff_delta]
  funext n
  simp [_root_.ArithmeticFunction.one_apply, _root_.LSeries.delta]





end IdealArithmeticFunction

namespace TauCeti.EulerProductData
end TauCeti.EulerProductData
section EulerProductData
open TauCeti TauCeti.EulerProductData

open _root_.TauCeti.IdealArithmeticFunction

variable (D : EulerProductData K) {s : ℂ}









/-- **Convergence of the finite Euler product.** Where the local Euler factors over a finite set
`S` of primes are absolutely convergent `LSeries`, so are the norm coefficients of the restriction
of `D` to `S`. -/
theorem solution (S : _root_.Finset (_root_.IsDedekindDomain.HeightOneSpectrum (𝓞 K)))
    (hS : ∀ P ∈ S, _root_.LSeriesSummable (D.localArithmeticFactor P) s) :
    _root_.LSeriesSummable (_root_.TauCeti.normCoeff K (_root_.TauCeti.IdealArithmeticFunction.supportedPart D.toIdealArithmeticFunction
      (S : _root_.Set (_root_.IsDedekindDomain.HeightOneSpectrum (𝓞 K))))) s := by
  classical
  induction S using _root_.Finset.induction_on with
  | empty =>
      rw [_root_.Finset.coe_empty, _root_.TauCeti.IdealArithmeticFunction.coe_normCoeff_supportedPart_empty D.isMultiplicative.map_one]
      refine _root_.summable_of_ne_finset_zero (s := {1}) fun n hn ↦ ?_
      simp only [_root_.Finset.mem_singleton] at hn
      simp [_root_.LSeries.term_delta, hn]
  | insert P S hPS ih =>
      rw [_root_.Finset.coe_insert, _root_.TauCeti.IdealArithmeticFunction.supportedPart_insert D.isMultiplicative (by simpa using hPS),
        _root_.TauCeti.normCoeff_convolution, _root_.TauCeti.IdealArithmeticFunction.normCoeff_supportedPart_singleton]
      refine _root_.ArithmeticFunction.LSeriesSummable_mul
        (ih fun Q hQ ↦ hS Q (_root_.Finset.mem_insert_of_mem hQ)) ?_
      rw [← D.localArithmeticFactor_eq P]
      exact hS P (_root_.Finset.mem_insert_self P S)



/-! ### The infinite Euler product -/







end EulerProductData

/-! ### Completely multiplicative weights -/

namespace TauCeti.MultiplicativeIdealWeight
end TauCeti.MultiplicativeIdealWeight
section MultiplicativeIdealWeight
open TauCeti TauCeti.MultiplicativeIdealWeight

open _root_.TauCeti.IdealArithmeticFunction

variable (χ : MultiplicativeIdealWeight K) {s : ℂ}















end MultiplicativeIdealWeight

/-! ### The Dedekind zeta function -/







end TauCeti

end
end
