-- Prove2me | solution 1 for TauCeti.MultiplicativeIdealWeight.logDeriv_LSeries_eq_tsum_prime_pow
-- status  : ACCEPTED   (prove)
-- author  : @riccardo.brasca
-- created : 2026-09-29T21:55:55.4898+00:00
-- url     : https://prove2.me/submissions/e9f1e99e-17cd-4bb3-b9fc-2fba2dc7b863

/- Transplanted from https://github.com/TauCetiProject/TauCeti at 948fe4751b1fe528b6d580c522ca5d743d47f185.
Original source copyright/license notices are retained below.
Generated exclusively from compiler declaration, command, and reference facts. -/
import Definitions.Def_TauCeti_NumberTheory_ArithmeticDirichletSeries_Basic
import Definitions.Def_TauCeti_NumberTheory_ArithmeticDirichletSeries_EulerProduct_Analytic
import Definitions.Def_TauCeti_NumberTheory_ArithmeticDirichletSeries_EulerProduct_Basic
import Definitions.Def_TauCeti_NumberTheory_ArithmeticDirichletSeries_EulerProduct_Data
import Definitions.Def_TauCeti_NumberTheory_ArithmeticDirichletSeries_NormCoeff
import Definitions.Def_TauCeti_NumberTheory_ArithmeticDirichletSeries_Regroup
import Definitions.Def_TauCeti_NumberTheory_ArithmeticDirichletSeries_Weight
import Mathlib.Algebra.Algebra.Subalgebra.Basic
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.CharZero.Infinite
import Mathlib.Algebra.IsPrimePow
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Ring.Subgroup
import Mathlib.Algebra.Ring.Subring.Basic
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Calculus.FDeriv.Defs
import Mathlib.Analysis.Calculus.LogDeriv
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.BranchLogRoot
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.Order
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Set.Card
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.ZMod.Units
import Mathlib.LinearAlgebra.Pi
import Mathlib.NumberTheory.ArithmeticFunction.Defs
import Mathlib.NumberTheory.ArithmeticFunction.LFunction
import Mathlib.NumberTheory.EulerProduct.ExpLog
import Mathlib.NumberTheory.LSeries.Convergence
import Mathlib.NumberTheory.LSeries.Convolution
import Mathlib.NumberTheory.LSeries.Deriv
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
import Theorems.Thm_Complex_summable_taylorSeries_neg_log
import Theorems.Thm_TauCeti_EulerProductData_eulerFactor_eq_tsum
import Theorems.Thm_TauCeti_EulerProductData_hasProd_eulerFactor
import Theorems.Thm_TauCeti_MultiplicativeIdealWeight_hasDerivAt_tsum_prime_pow

section
set_option autoImplicit true
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
/-!
# Holomorphic branches of `log` and of `n`-th roots on a simply connected domain

Mathlib's `Complex.exists_continuousOn_eqOn_exp_comp` produces a **continuous** branch of `log ∘ g`
on a simply connected open set. The Riemann-mapping argument needs a **holomorphic** one. This file
supplies that upgrade for the logarithm, consuming Mathlib's branch rather than rebuilding it, and
then obtains the `n`-th root from it directly as `exp (L / n)`.

Note that the root branch is *not* an upgrade of Mathlib's `Complex.exists_continuousOn_pow_eq`,
which this file does not use: once the logarithm branch is holomorphic, `exp (L / n)` is holomorphic
by composition and satisfies `(exp (L / n)) ^ n = exp L = g` outright, so routing through a separate
continuous root branch would add a second continuity-to-holomorphy argument for no gain.

The upgrade is local and purely formal. Near a point `z₀`, the continuous branch `L` agrees with
`logBranch w₀ ∘ g` where `w₀ = L z₀`, the branch of the logarithm based at `w₀`: that composite is
holomorphic (the argument sits near `1`, inside the slit plane, where `Complex.log` is), and it
agrees with `L` because continuity of `L` confines `L z - w₀` to the strip `|im| < π` on which that
branch inverts `Complex.exp`. So no new analysis is involved — only the observation that a
continuous logarithm of a holomorphic nonvanishing function is automatically holomorphic.

## Attribution and upstream coordination

The mathematics here is an upgrade of prior Mathlib work, not a first proof. The logarithm and
zero-free root branches rest on two efforts of Yury Kudryashov's; the germ statement rests in
addition on Mathlib's order-of-vanishing formalization.

*The branch itself* is Mathlib's: `Complex.exists_continuousOn_eqOn_exp_comp` in
`Mathlib.Analysis.Complex.BranchLogRoot` (© Yury Kudryashov) supplies the continuous logarithm
branch on a simply connected domain, which this file consumes rather than rebuilds. What
`TauCeti.exists_differentiableOn_eqOn_exp_comp` and `TauCeti.exists_differentiableOn_pow_eq` add to
it is the continuity-to-holomorphy upgrade. The `n`-th root is *not* obtained from Mathlib's
continuous root API (`Complex.exists_continuousOn_pow_eq` is never used here): it is derived as
`exp (L / n)` from the upgraded holomorphic logarithm branch `L`.

*The order of vanishing* is Mathlib's too: `Mathlib.Analysis.Analytic.Order` (© Vincent Beffara;
authors Vincent Beffara and Stefan Kebekus) formalizes `analyticOrderAt` and the factorization
theory around it, on which `TauCeti.exists_eventuallyEq_pow_iff_dvd` rests throughout.
`AnalyticAt.analyticOrderAt_eq_natCast` supplies the factorization of a germ of finite order,
`analyticOrderAt_eq_top` identifies the germ of order `⊤` as the one vanishing near `z₀`, and
`analyticOrderAt_pow` gives the converse direction outright. What is added here is only the
assembly of those with the root branch above.

*The consumer* is the Riemann mapping construction in `Mathlib.Analysis.Complex.RiemannMapping`
(© Yury Kudryashov), whose `Complex.exists_mapsTo_unitBall_injOn_deriv_ne_zero` performs the same
square-root step that the sibling file `DiscInjection.lean` re-derives on top of this API; see its
docstring for why that lemma cannot be named by an importer.

The Riemann mapping theorem is being formalized upstream at
[mathlib4#33505](https://github.com/leanprover-community/mathlib4/pull/33505), which proves
holomorphic log / `n`-th-root statements (`exists_branch_log`, `exists_branch_nthRoot`)
**internally, as private lemmas**, alongside the argument principle, Hurwitz and Montel. The
`ConformalMapping` roadmap's stated contribution at these layers is therefore *named, reusable API*
rather than first proof. Accordingly the two branch declarations here are a **temporary shim**: when
the human-curated Mathlib versions land, those should be deleted and every downstream consumer
refactored onto them. That does not extend to `TauCeti.exists_eventuallyEq_pow_iff_dvd`: the
upstream statements are zero-free, like the ones they replace, so they do not subsume a germ that
vanishes.

## Roots of a germ that vanishes

The root branch needs `g` to be zero-free, so on its own it says nothing about a germ that
vanishes. Locally that gap closes by factoring the zero out: `A z = (z - z₀) ^ m • g z` with
`g z₀ ≠ 0`, so an `n`-th root of the germ exists exactly when `n` divides its order of vanishing
(`TauCeti.exists_eventuallyEq_pow_iff_dvd`), namely `(z - z₀) ^ (m / n)` times the branch above
applied to `g`. This weakens the zero-free hypothesis — the case of order `0` — to the
divisibility condition, and the converse direction shows the condition is sharp. The germ that
vanishes identically near `z₀`, of order `⊤`, is its own `n`-th root.

## Main statements

* `TauCeti.exists_differentiableOn_eqOn_exp_comp` — a holomorphic branch of `log ∘ g`.
* `TauCeti.exists_differentiableOn_pow_eq` — a holomorphic branch of `ⁿ√g`.
* `TauCeti.exists_eventuallyEq_pow_iff_dvd` — a holomorphic germ has a holomorphic `n`-th root iff
  `n` divides its order of vanishing.
* `TauCeti.deriv_eq_logDeriv_of_eqOn_exp_comp` — the derivative of a branch of the logarithm is the
  logarithmic derivative, and so does not depend on which branch was chosen.
-/

 section

namespace TauCeti

open Complex Set

















/-- **The derivative of a branch is the logarithmic derivative.**  Wherever a holomorphic `f`
satisfies `exp ∘ f = g` on an open set, `f' = g' / g` there.  This is what makes a branch of the
logarithm useful even though `exp` determines it only up to `2πi ℤ`: the ambiguity is a locally
constant additive one, so it disappears on differentiating. -/
theorem deriv_eq_logDeriv_of_eqOn_exp_comp {U : Set ℂ} (hUo : IsOpen U) {f g : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f U) (h : EqOn (Complex.exp ∘ f) g U) {z : ℂ} (hz : z ∈ U) :
    deriv f z = logDeriv g z := by
  have hfz : DifferentiableAt ℂ f z := (hf z hz).differentiableAt (hUo.mem_nhds hz)
  have heq : (Complex.exp ∘ f) =ᶠ[nhds z] g :=
    Filter.eventuallyEq_of_mem (hUo.mem_nhds hz) fun w hw ↦ h hw
  rw [← (logDeriv_congr_nhds heq).eq_of_nhds, logDeriv_comp Complex.differentiableAt_exp hfz,
    Complex.logDeriv_exp]
  simp

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
# The Taylor series of `-log (1 - ·)` summed over a family

Mathlib's `Complex.hasSum_taylorSeries_neg_log'` expands `-log (1 - z)` as `∑' e, z ^ (e+1)/(e+1)`
for a single `z` of modulus less than one.  This file sums that over a family `r : ι → ℂ`: the
double family indexed by `ι × ℕ` is summable, so the sum may be regrouped fibrewise and the
prime-power-style sum over pairs equals the sum of local logarithms.

Both hypotheses are needed.  `∀ i, ‖r i‖ < 1` alone does not suffice: the fibre at `i` sums to
`‖r i‖ / (1 - ‖r i‖)`, which is dominated by `‖r i‖` only when `‖r i‖` is bounded away from `1`,
and summability of `r` is what supplies that uniformity.  That fibrewise argument is not carried out
here: it is `TauCeti.summable_mul_norm_pow_succ`, stated for a seminormed additive group and an
arbitrary real weight, and this file uses it at weight `1`.

## Main results

* `Complex.summable_taylorSeries_neg_log`: for a summable `r : ι → ℂ` with every `‖r i‖ < 1`, the
  family `(i, e) ↦ r i ^ (e + 1) / (e + 1)` is summable over `ι × ℕ`.
* `Complex.tsum_taylorSeries_neg_log`: its sum over `ι × ℕ` is `∑' i, -log (1 - r i)`.
-/

 section

namespace Complex




/-- **The double sum is the sum of the local logarithms.**  For a summable `r : ι → ℂ` with every
`‖r i‖ < 1`, summing the Taylor series of `-log (1 - r i)` over `ι × ℕ` gives `∑' i, -log (1 - r i)`
— the fibrewise regrouping that `summable_taylorSeries_neg_log` licenses. -/
theorem tsum_taylorSeries_neg_log {ι : Type*} {r : ι → ℂ} (hr : Summable r)
    (h1 : ∀ i, ‖r i‖ < 1) :
    ∑' ie : ι × ℕ, r ie.1 ^ (ie.2 + 1) / ((ie.2 : ℂ) + 1) = ∑' i, -Complex.log (1 - r i) := by
  have hfib : ∀ i, HasSum (fun e : ℕ ↦ r i ^ (e + 1) / ((e : ℂ) + 1))
      (-Complex.log (1 - r i)) := fun i ↦ hasSum_taylorSeries_neg_log' (h1 i)
  exact ((summable_taylorSeries_neg_log hr h1).hasSum.prod_fiberwise hfib).tsum_eq.symm

end Complex

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
# Regrouping an ideal-indexed Dirichlet series by absolute norm

An `TauCeti.IdealArithmeticFunction K` has two Dirichlet series attached to it: the series indexed
by the nonzero integral ideals of `𝓞 K`, whose terms are `TauCeti.idealTerm`, and the Mathlib
`LSeries` of the regrouped coefficients `TauCeti.normCoeff`. This file proves that the second is
obtained from the first by summing over the finite absolute-norm fibres, so that absolute
convergence of the ideal-indexed series transfers to the `LSeries` together with the value of the
sum.

## Main definitions

* `TauCeti.idealTerm f s I` is the term `f I / N(I) ^ s` of the ideal-indexed Dirichlet series.
* `TauCeti.idealAbscissaOfAbsConv f` is the abscissa of absolute convergence of that series, the
  ideal-indexed analogue of Mathlib's `LSeries.abscissaOfAbsConv`.

## Main results

* `TauCeti.regroupByNorm`: if the ideal-indexed series has sum `L` at `s`, then so does the
  `LSeries` of `TauCeti.normCoeff f`; `TauCeti.LSeriesSummable_normCoeff` and
  `TauCeti.LSeries_normCoeff` are the summability and value statements it packages.
* `TauCeti.summable_log_absNorm_mul_norm_idealTerm_of_re_lt_re`: weighting the ideal terms
  by `log N(I)` keeps them summable strictly to the right of a point of absolute convergence.
* `TauCeti.abscissaOfAbsConv_normCoeff_le`: consequently the grouped abscissa of absolute
  convergence is at most the ideal-indexed one.
* `TauCeti.summable_idealTerm_of_norm_normCoeff_eq_sum_norm`: the converse holds whenever no
  cancellation occurs inside a norm fibre. `TauCeti.summable_idealTerm_of_nonneg` and
  `TauCeti.idealAbscissaOfAbsConv_eq_abscissaOfAbsConv` specialize it to the case where every
  *individual ideal summand* is nonnegative, where moreover the two abscissae agree.

## Implementation notes

The regrouping is an instance of Mathlib's `HasSum.tsum_fiberwise` along the absolute norm
`fun I ↦ Ideal.absNorm (I : Ideal (𝓞 K))`, whose fibres are the finite sets
`TauCeti.normFiber K n`. Absolute convergence of the ideal-indexed series is expressed as plain
`Summable`, which for a complex-valued family is unconditional convergence and hence absolute
convergence; no rearrangement hypothesis is therefore needed for the transfer.

The converse is proved through `summable_partition` applied to the norms of the terms. All it
needs about `f` is that the norm of each grouped coefficient is the sum of the norms over its
fibre — the absence of cancellation inside the fibre. Nonnegativity of every ideal summand is one
way to secure that, through `TauCeti.norm_normCoeff_eq_sum_norm_of_nonneg`; it is the step that
fails under cancellation, as the rejection test
`TauCeti.exists_forall_normCoeff_nonneg_not_forall_nonneg` records. That test is a statement about
`TauCeti.normCoeff` alone, so it lives with that definition rather than here.

## Roadmap role

This is Layer **1.2** of `TauCetiRoadmap/ArithmeticDirichletSeries/README.md`; the required worked
example 9 accompanies it in `TauCeti/NumberTheory/ArithmeticDirichletSeries/NormCoeff.lean`. The
exact value of the abscissa for the trivial weight is deliberately not proved here: its divergence
input is the Layer 5 ideal count of
`TauCeti/NumberTheory/ArithmeticDirichletSeries/Estimates.lean`.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter VII.
* G. Tenenbaum, *Introduction to Analytic and Probabilistic Number Theory*, Chapters II--III.
-/

 section

namespace TauCeti

open scoped _root_.nonZeroDivisors _root_.NumberField _root_.ComplexOrder

variable (K : Type*) [Field K] [NumberField K]

/-! ### The ideal-indexed term -/



/-- Defining equation of `TauCeti.idealTerm`. -/
theorem idealTerm_def (f : IdealArithmeticFunction K) (s : ℂ) (I : (Ideal (𝓞 K))⁰) :
    idealTerm K f s I = f I / (Ideal.absNorm (I : Ideal (𝓞 K)) : ℂ) ^ s :=
  (rfl)

/-- The absolute value of an ideal term depends on `s` only through its real part. -/
@[simp]
theorem norm_idealTerm (f : IdealArithmeticFunction K) (s : ℂ) (I : (Ideal (𝓞 K))⁰) :
    ‖idealTerm K f s I‖ = ‖f I‖ / (Ideal.absNorm (I : Ideal (𝓞 K)) : ℝ) ^ s.re := by
  rw [idealTerm_def, norm_div,
    Complex.norm_natCast_cpow_of_pos (Ideal.absNorm_pos_of_nonZeroDivisors I)]

/-- Ideal terms decrease in absolute value as the real part of `s` grows, because every nonzero
integral ideal has absolute norm at least one. -/
theorem norm_idealTerm_le_of_re_le_re (f : IdealArithmeticFunction K) {s s' : ℂ}
    (h : s.re ≤ s'.re) (I : (Ideal (𝓞 K))⁰) :
    ‖idealTerm K f s' I‖ ≤ ‖idealTerm K f s I‖ := by
  have h₁ : (1 : ℝ) ≤ (Ideal.absNorm (I : Ideal (𝓞 K)) : ℝ) := by
    exact_mod_cast Ideal.absNorm_pos_of_nonZeroDivisors I
  have h₀ : (0 : ℝ) < (Ideal.absNorm (I : Ideal (𝓞 K)) : ℝ) ^ s.re :=
    Real.rpow_pos_of_pos (by linarith) _
  simp only [norm_idealTerm]
  gcongr

/-- Absolute convergence of the ideal-indexed series propagates to the right. -/
theorem summable_idealTerm_of_re_le_re {f : IdealArithmeticFunction K} {s s' : ℂ}
    (h : s.re ≤ s'.re) (hf : Summable (idealTerm K f s)) : Summable (idealTerm K f s') := by
  rw [← summable_norm_iff] at hf ⊢
  exact hf.of_nonneg_of_le (fun _ ↦ norm_nonneg _) (norm_idealTerm_le_of_re_le_re K f h)





/-! ### Regrouping -/











/-! ### The ideal-indexed abscissa of absolute convergence -/



/-- Defining equation of `TauCeti.idealAbscissaOfAbsConv`. -/
theorem idealAbscissaOfAbsConv_def (f : IdealArithmeticFunction K) :
    idealAbscissaOfAbsConv K f = sInf (Real.toEReal '' {x : ℝ | Summable (idealTerm K f x)}) :=
  (rfl)

/-- **A point of absolute convergence strictly to the left.**  Strictly to the right of the
ideal-indexed abscissa of absolute convergence there is a real point, still strictly to the left,
at which the ideal-indexed series converges absolutely.

This is the form in which the abscissa is consumed by estimates that need room to the left, such
as the logarithmic weights produced by differentiation. -/
theorem exists_summable_idealTerm_of_idealAbscissaOfAbsConv_lt_re
    {f : IdealArithmeticFunction K} {s : ℂ} (hs : idealAbscissaOfAbsConv K f < s.re) :
    ∃ y : ℝ, Summable (idealTerm K f y) ∧ y < s.re := by
  simpa [idealAbscissaOfAbsConv, sInf_lt_iff] using hs

/-- The ideal-indexed series converges absolutely strictly to the right of its abscissa. -/
theorem summable_idealTerm_of_idealAbscissaOfAbsConv_lt_re {f : IdealArithmeticFunction K} {s : ℂ}
    (hs : idealAbscissaOfAbsConv K f < s.re) : Summable (idealTerm K f s) := by
  obtain ⟨y, hy, hys⟩ := exists_summable_idealTerm_of_idealAbscissaOfAbsConv_lt_re K hs
  exact summable_idealTerm_of_re_le_re K (Complex.ofReal_re y ▸ hys.le) hy

/-- A point of absolute convergence bounds the ideal-indexed abscissa. -/
theorem idealAbscissaOfAbsConv_le {f : IdealArithmeticFunction K} {s : ℂ}
    (h : Summable (idealTerm K f s)) : idealAbscissaOfAbsConv K f ≤ s.re :=
  sInf_le ⟨s.re, summable_idealTerm_of_re_le_re K (by simp) h, rfl⟩



/-! ### The converse, in the absence of cancellation inside norm fibres -/











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



/-- A prime power, as a nonzero integral ideal, has the expected underlying ideal. -/
@[simp]
theorem coe_primeIdealPow (P : HeightOneSpectrum (𝓞 K)) (e : ℕ) :
    (primeIdealPow P e : Ideal (𝓞 K)) = P.asIdeal ^ e :=
  (rfl)

variable [NumberField K]

/-- The absolute norm is multiplicative on prime powers. -/
theorem absNorm_primeIdealPow (P : HeightOneSpectrum (𝓞 K)) (e : ℕ) :
    Ideal.absNorm (primeIdealPow P e : Ideal (𝓞 K)) = Ideal.absNorm P.asIdeal ^ e := by
  rw [coe_primeIdealPow, map_pow]

omit [NumberField K] in
/-- Distinct primes give distinct first powers, so a family indexed by the primes is a subfamily
of one indexed by the nonzero ideals. -/
theorem primeIdealPow_one_injective :
    Function.Injective fun P : HeightOneSpectrum (𝓞 K) ↦ primeIdealPow P 1 := fun P Q h ↦
  HeightOneSpectrum.asIdeal_injective
    (by simpa only [coe_primeIdealPow, pow_one] using
      congrArg (Subtype.val : (Ideal (𝓞 K))⁰ → Ideal (𝓞 K)) h)

/-- Distinct exponents give distinct prime powers. -/
theorem primeIdealPow_injective (P : HeightOneSpectrum (𝓞 K)) :
    Function.Injective (primeIdealPow P) := fun m n h ↦
  Nat.pow_right_injective (NumberField.HeightOneSpectrum.one_lt_absNorm P)
    (by simpa only [absNorm_primeIdealPow] using
      congrArg (fun I : (Ideal (𝓞 K))⁰ ↦ Ideal.absNorm (I : Ideal (𝓞 K))) h)

end IsDedekindDomain.HeightOneSpectrum

namespace TauCeti



namespace IdealArithmeticFunction

variable {K : Type*} [Field K]

variable [NumberField K]



























/-! ### Finite Euler products -/



variable {f : IdealArithmeticFunction K} {S : Set (HeightOneSpectrum (𝓞 K))}
  {A : (Ideal (𝓞 K))⁰}































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



























/-- The coefficient function underlying the Euler-product data of a multiplicative ideal weight. -/
@[simp]
theorem toIdealArithmeticFunction_ofMultiplicativeIdealWeight (χ : MultiplicativeIdealWeight K) :
    (ofMultiplicativeIdealWeight χ).toIdealArithmeticFunction = χ.toIdealArithmeticFunction := by
  funext I
  rfl





















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

variable {K : Type*} [Field K] [NumberField K]











end IsDedekindDomain.HeightOneSpectrum

namespace TauCeti

open scoped _root_.nonZeroDivisors _root_.ComplexOrder

variable {K : Type*} [Field K] [NumberField K]

namespace EulerProductData

open _root_.TauCeti.IdealArithmeticFunction

variable (D : EulerProductData K) {s : ℂ}

/-! ### The local Euler factor -/







end EulerProductData

namespace IdealArithmeticFunction

variable {f : IdealArithmeticFunction K} {s : ℂ}

/-! ### Restriction to a set of primes, analytically -/













/-- **The prime terms are a subseries of the ideal terms.** Each height-one prime contributes its
own ideal as the `e = 1` member of its power series, and distinct primes give distinct ideals, so
absolute convergence over ideals restricts to the primes. Multiplicativity plays no part. -/
theorem summable_idealTerm_primeIdealPow_one (hs : Summable (idealTerm K f s)) :
    Summable fun P : HeightOneSpectrum (𝓞 K) ↦ idealTerm K f s (P.primeIdealPow 1) :=
  hs.comp_injective HeightOneSpectrum.primeIdealPow_one_injective

end IdealArithmeticFunction

namespace EulerProductData

open _root_.TauCeti.IdealArithmeticFunction

variable (D : EulerProductData K) {s : ℂ}













/-! ### The infinite Euler product -/







end EulerProductData

/-! ### Completely multiplicative weights -/

namespace MultiplicativeIdealWeight

open _root_.TauCeti.IdealArithmeticFunction

variable (χ : MultiplicativeIdealWeight K) {s : ℂ}

/-- The ideal terms of a completely multiplicative weight along the powers of a prime form a
geometric progression. -/
@[simp]
theorem idealTerm_toIdealArithmeticFunction_primeIdealPow (P : HeightOneSpectrum (𝓞 K)) (e : ℕ)
    (s : ℂ) :
    idealTerm K χ.toIdealArithmeticFunction s (P.primeIdealPow e) =
      (χ P.asIdeal / (Ideal.absNorm P.asIdeal : ℂ) ^ s) ^ e := by
  rw [idealTerm_def, toIdealArithmeticFunction_apply,
    P.absNorm_primeIdealPow, P.coe_primeIdealPow,
    map_pow, Nat.cast_pow, ← Complex.natCast_cpow_natCast_mul,
    Complex.cpow_nat_mul, div_pow]

/-- **The local ratio of a convergent weight is a contraction.** Absolute convergence of the
ideal-indexed Dirichlet series forces the geometric ratio at each prime to have modulus less than
one, because the powers of that prime already contribute a geometric subseries. -/
theorem norm_div_lt_one_of_summable_idealTerm
    (hs : Summable (idealTerm K χ.toIdealArithmeticFunction s))
    (P : HeightOneSpectrum (𝓞 K)) :
    ‖χ P.asIdeal / (Ideal.absNorm P.asIdeal : ℂ) ^ s‖ < 1 := by
  rw [← summable_geometric_iff_norm_lt_one]
  exact (hs.comp_injective P.primeIdealPow_injective).congr fun e ↦
    idealTerm_toIdealArithmeticFunction_primeIdealPow χ P e s

/-- **The local ratios are summable over the primes.** The multiplicative specialisation of
`IdealArithmeticFunction.summable_idealTerm_primeIdealPow_one`: at a prime the ideal term *is* the
ratio `χ(P) N(P)⁻ˢ`. -/
theorem summable_div_of_summable_idealTerm
    (hs : Summable (idealTerm K χ.toIdealArithmeticFunction s)) :
    Summable fun P : HeightOneSpectrum (𝓞 K) ↦
      χ P.asIdeal / (Ideal.absNorm P.asIdeal : ℂ) ^ s :=
  (IdealArithmeticFunction.summable_idealTerm_primeIdealPow_one hs).congr fun P ↦ by
    simp [idealTerm_toIdealArithmeticFunction_primeIdealPow χ P 1 s]

/-- Absolute convergence puts every local ratio `χ(P) N(P)⁻ˢ` strictly inside the unit disc, so no
local Euler factor has a vanishing denominator. -/
theorem one_sub_div_ne_zero_of_summable_idealTerm
    (hs : Summable (idealTerm K χ.toIdealArithmeticFunction s)) (P : HeightOneSpectrum (𝓞 K)) :
    1 - χ P.asIdeal / (Ideal.absNorm P.asIdeal : ℂ) ^ s ≠ 0 := fun h ↦ by
  have hlt := norm_div_lt_one_of_summable_idealTerm χ hs P
  rw [sub_eq_zero] at h
  rw [← h] at hlt
  simp at hlt

/-- The local Euler factor of a completely multiplicative weight is the geometric closed form
`(1 - χ(P) N(P)⁻ˢ)⁻¹`. -/
theorem eulerFactor_ofMultiplicativeIdealWeight
    (P : HeightOneSpectrum (𝓞 K))
    (hP : ‖χ P.asIdeal / (Ideal.absNorm P.asIdeal : ℂ) ^ s‖ < 1) :
    (EulerProductData.ofMultiplicativeIdealWeight χ).eulerFactor P s =
      (1 - χ P.asIdeal / (Ideal.absNorm P.asIdeal : ℂ) ^ s)⁻¹ := by
  rw [EulerProductData.eulerFactor_eq_tsum,
    EulerProductData.toIdealArithmeticFunction_ofMultiplicativeIdealWeight,
    tsum_congr fun e ↦ idealTerm_toIdealArithmeticFunction_primeIdealPow χ P e s]
  exact tsum_geometric_of_norm_lt_one hP

/-- **The Euler product of a completely multiplicative ideal weight.** -/
theorem hasProd_eulerFactor (hs : Summable (idealTerm K χ.toIdealArithmeticFunction s)) :
    HasProd (fun P : HeightOneSpectrum (𝓞 K) ↦
        (1 - χ P.asIdeal / (Ideal.absNorm P.asIdeal : ℂ) ^ s)⁻¹)
      (LSeries (normCoeff K χ.toIdealArithmeticFunction) s) := by
  have hfun : (fun P : HeightOneSpectrum (𝓞 K) ↦
      (1 - χ P.asIdeal / (Ideal.absNorm P.asIdeal : ℂ) ^ s)⁻¹) =
      fun P ↦ (EulerProductData.ofMultiplicativeIdealWeight χ).eulerFactor P s :=
    funext fun P ↦ (eulerFactor_ofMultiplicativeIdealWeight χ P
      (norm_div_lt_one_of_summable_idealTerm χ hs P)).symm
  rw [hfun]
  have hprod := (EulerProductData.ofMultiplicativeIdealWeight χ).hasProd_eulerFactor
    (s := s) (by
      simpa only [EulerProductData.toIdealArithmeticFunction_ofMultiplicativeIdealWeight] using hs)
  simpa only [EulerProductData.toIdealArithmeticFunction_ofMultiplicativeIdealWeight] using hprod



end MultiplicativeIdealWeight

/-! ### The Dedekind zeta function -/







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
# The Euler product over the primes of a number field, in exponential form

Mathlib's `EulerProduct.exp_tsum_primes_log_eq_tsum` writes the Euler product of a completely
multiplicative `f : ℕ →*₀ ℂ` as `exp (∑' p, -log (1 - f p))`. This file is the ideal-indexed
analogue, over the height-one primes of the ring of integers of a number field, mirroring the way
`TauCeti.MultiplicativeIdealWeight.hasProd_eulerFactor` mirrors Mathlib's product form.

The logarithm is taken factor by factor, using the principal value: absolute convergence of the
ideal-indexed series forces each local ratio into the open unit disc, where `Complex.log (1 - ·)`
is defined without choosing anything.

**What this does not give.** `exp` is not injective, so an identity of the form `exp t = L`
determines `t` only modulo `2πi ℤ`; these theorems therefore do not exhibit a logarithm *of* the
`L`-series, and in particular are not a holomorphic branch on a region.
`TauCeti.MultiplicativeIdealWeight.LSeries_ne_zero_of_summable_idealTerm` supplies nonvanishing
pointwise, wherever the ideal-indexed series converges absolutely; a branch needs more than that —
a simply connected zero-free region on which to choose one — and is not constructed here.

## Main results

* `TauCeti.MultiplicativeIdealWeight.summable_neg_log_one_sub`: summability of the
  prime-indexed logarithm sum wherever the ideal-indexed series converges absolutely.
* `TauCeti.MultiplicativeIdealWeight.exp_tsum_neg_log_one_sub_eq_LSeries`: the `L`-series as the
  exponential of a sum of principal logarithms over the primes.
* `TauCeti.MultiplicativeIdealWeight.tsum_prime_pow_eq_tsum_neg_log_one_sub`: that sum re-indexed
  by a prime and an exponent, as an identity of complex numbers.
* `TauCeti.MultiplicativeIdealWeight.exp_tsum_prime_pow_eq_LSeries`: the exponential form of the
  re-indexed sum.
-/

 section

namespace TauCeti

open _root_.Complex _root_.IsDedekindDomain

open scoped _root_.NumberField

namespace MultiplicativeIdealWeight

open _root_.TauCeti.IdealArithmeticFunction

variable {K : Type*} [Field K] [NumberField K] (χ : MultiplicativeIdealWeight K) {s : ℂ}

/-- The prime-indexed sum of principal logarithms converges whenever the ideal-indexed series
of a multiplicative ideal weight converges absolutely. -/
theorem summable_neg_log_one_sub
    (hs : Summable (idealTerm K χ.toIdealArithmeticFunction s)) :
    Summable (fun P : HeightOneSpectrum (𝓞 K) ↦
      -log (1 - χ P.asIdeal / (Ideal.absNorm P.asIdeal : ℂ) ^ s)) :=
  (Summable.clog_one_sub (χ.summable_div_of_summable_idealTerm hs)).neg

/-- **The Euler product in exponential form.** For a completely multiplicative ideal weight whose
ideal-indexed series converges absolutely at `s`, the `L`-series is the exponential of the sum of
principal logarithms `-log (1 - χ(P) N(P)⁻ˢ)` over the height-one primes.

The sum is not thereby a logarithm of the `L`-series: `exp` identifies it only modulo `2πi ℤ`.
This is the number-field analogue of Mathlib's `EulerProduct.exp_tsum_primes_log_eq_tsum`, and
carries the same limitation. -/
theorem exp_tsum_neg_log_one_sub_eq_LSeries
    (hs : Summable (idealTerm K χ.toIdealArithmeticFunction s)) :
    exp (∑' P : HeightOneSpectrum (𝓞 K),
        -log (1 - χ P.asIdeal / (Ideal.absNorm P.asIdeal : ℂ) ^ s)) =
      LSeries (normCoeff K χ.toIdealArithmeticFunction) s := by
  have hne := χ.one_sub_div_ne_zero_of_summable_idealTerm hs
  have H := (χ.summable_neg_log_one_sub hs).hasSum.cexp.tprod_eq
  simp only [Function.comp_apply, exp_neg, exp_log (hne _)] at H
  exact H.symm.trans (χ.hasProd_eulerFactor hs).tprod_eq

/-- **The prime-power sum is the prime-indexed logarithm sum.**  Substituting the Taylor series of
`-log (1 - ·)` at each prime and regrouping over the primes identifies the two sums *as complex
numbers*, before any exponential is taken.  This is the statement a consumer needs in order to
rewrite one into the other; the exponential form below follows from it. -/
theorem tsum_prime_pow_eq_tsum_neg_log_one_sub
    (hs : Summable (idealTerm K χ.toIdealArithmeticFunction s)) :
    ∑' pe : HeightOneSpectrum (𝓞 K) × ℕ,
        (χ pe.1.asIdeal / (Ideal.absNorm pe.1.asIdeal : ℂ) ^ s) ^ (pe.2 + 1) / ((pe.2 : ℂ) + 1) =
      ∑' P : HeightOneSpectrum (𝓞 K),
        -log (1 - χ P.asIdeal / (Ideal.absNorm P.asIdeal : ℂ) ^ s) :=
  tsum_taylorSeries_neg_log
    (r := fun P : HeightOneSpectrum (𝓞 K) ↦ χ P.asIdeal / (Ideal.absNorm P.asIdeal : ℂ) ^ s)
    (χ.summable_div_of_summable_idealTerm hs) (χ.norm_div_lt_one_of_summable_idealTerm hs)

/-- **The Euler product expanded over prime powers.**  The `L`-series is the exponential of the
sum over pairs `(P, e)` of a prime and an exponent.  The caveat above applies unchanged: `exp` is
not injective, so this identifies the double sum only modulo `2πi ℤ` and does not exhibit a
logarithm of the `L`-series. -/
theorem exp_tsum_prime_pow_eq_LSeries
    (hs : Summable (idealTerm K χ.toIdealArithmeticFunction s)) :
    exp (∑' pe : HeightOneSpectrum (𝓞 K) × ℕ,
        (χ pe.1.asIdeal / (Ideal.absNorm pe.1.asIdeal : ℂ) ^ s) ^ (pe.2 + 1) / ((pe.2 : ℂ) + 1)) =
      LSeries (normCoeff K χ.toIdealArithmeticFunction) s := by
  rw [χ.tsum_prime_pow_eq_tsum_neg_log_one_sub hs, χ.exp_tsum_neg_log_one_sub_eq_LSeries hs]

end MultiplicativeIdealWeight

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
# Derivatives of ideal Euler factors and logarithmic expansions

For general `TauCeti.EulerProductData`, this file first differentiates each local Euler factor.
The derivative at a prime `P` is the exact prime-power series

`-∑ e, log N(P ^ e) · D(P ^ e) / N(P ^ e) ^ s`.

This is the local analytic input for expressing the logarithmic derivative of a general ideal
Euler product in terms of its prime-power data. The second part of the file specializes to a
completely multiplicative weight, where the logarithm itself has a geometric Taylor expansion and
can be differentiated after summing over all primes and exponents.

`TauCeti.MultiplicativeIdealWeight.tsum_prime_pow_eq_tsum_neg_log_one_sub` expands the sum of local
logarithms over the prime powers `(P, e)`.  This file differentiates that expansion in `s`, term by
term, on the open half-plane where the ideal-indexed series converges absolutely.

Each term `(χ(P) N(P)⁻ˢ) ^ (e+1) / (e+1)` differentiates to `-log N(P) * (χ(P) N(P)⁻ˢ) ^ (e+1)`, so
the differentiated family is the undivided one weighted by `-log N(P)`.  Termwise differentiation of
a sum needs a summable majorant valid across a neighbourhood rather than at the single point, and
the half-plane supplies it: strictly to the right of a point of absolute convergence the weight
`log N(P)` is absorbed, which is `summable_log_absNorm_mul_norm_idealTerm_of_re_lt_re`, and the
exponent direction is geometric, which is `TauCeti.summable_mul_norm_pow_succ`.

`EulerProduct/Branch.lean` identifies the derivative of a *branch* of the logarithm with the
logarithmic derivative of the `L`-series.  That is an abstract identification; this file gives the
prime-power series the derivative is equal to.

## Main results

* `TauCeti.EulerProductData.hasDerivAt_eulerFactor`: a general local Euler factor differentiates
  termwise into the negative of its log-weighted prime-power series.
* `TauCeti.EulerProductData.logDeriv_eulerFactor_eq`: the local factor's logarithmic derivative is
  the negative quotient of that prime-power series by the local factor.
* `TauCeti.MultiplicativeIdealWeight.hasDerivAt_tsum_prime_pow`: the prime-power expansion
  differentiates termwise, strictly right of the abscissa of absolute convergence.
* `TauCeti.MultiplicativeIdealWeight.logDeriv_LSeries_eq_tsum_prime_pow`: that derivative **is**
  the logarithmic derivative of the `L`-series.
-/

 section

namespace TauCeti
end TauCeti
section TauCeti
open TauCeti

open Complex IsDedekindDomain

open scoped nonZeroDivisors NumberField

namespace TauCeti.EulerProductData
end TauCeti.EulerProductData
section EulerProductData
open TauCeti TauCeti.EulerProductData

open IdealArithmeticFunction

variable {K : Type*} [Field K] [NumberField K] (D : EulerProductData K)

/-! ### Derivative of a general local Euler factor -/











end EulerProductData

namespace TauCeti.MultiplicativeIdealWeight
end TauCeti.MultiplicativeIdealWeight
section MultiplicativeIdealWeight
open TauCeti TauCeti.MultiplicativeIdealWeight

open IdealArithmeticFunction

variable {K : Type*} [Field K] [NumberField K] (χ : MultiplicativeIdealWeight K)









/-- **The logarithmic derivative of the `L`-series, as a prime-power series.**  Strictly to the
right of a point of absolute convergence,

`logDeriv L(s) = ∑' (P, e), -log N(P) · (χ(P) N(P)⁻ˢ) ^ (e+1)`

strictly to the right of the abscissa of absolute convergence.

The prime-power expansion is a branch of the logarithm of the `L`-series there — its exponential
is the `L`-series, by `exp_tsum_prime_pow_eq_LSeries` — and the derivative of any such branch is
the logarithmic derivative, the branch ambiguity being locally constant.

This is what lets a density argument work with the logarithmic derivative termwise over prime
powers, rather than with the `L`-series itself. -/
theorem solution {s : ℂ}
    (hs : _root_.TauCeti.idealAbscissaOfAbsConv K χ.toIdealArithmeticFunction < s.re) :
    _root_.logDeriv (_root_.LSeries (_root_.TauCeti.normCoeff K χ.toIdealArithmeticFunction)) s
      = ∑' pe : _root_.IsDedekindDomain.HeightOneSpectrum (𝓞 K) × ℕ,
        -(_root_.Complex.log (_root_.Ideal.absNorm pe.1.asIdeal : ℂ)
          * (χ pe.1.asIdeal / (_root_.Ideal.absNorm pe.1.asIdeal : ℂ) ^ s) ^ (pe.2 + 1)) := by
  obtain ⟨y, hy, hys⟩ : ∃ y : ℝ, _root_.Summable (_root_.TauCeti.idealTerm K χ.toIdealArithmeticFunction y)
      ∧ y < s.re := by simpa [_root_.TauCeti.idealAbscissaOfAbsConv_def, _root_.sInf_lt_iff] using hs
  set U : _root_.Set ℂ := {z : ℂ | y < z.re} with hU
  set f : ℂ → ℂ := fun z ↦ ∑' pe : _root_.IsDedekindDomain.HeightOneSpectrum (𝓞 K) × ℕ,
    (χ pe.1.asIdeal / (_root_.Ideal.absNorm pe.1.asIdeal : ℂ) ^ z) ^ (pe.2 + 1) / ((pe.2 : ℂ) + 1) with hf
  have hmem : ∀ z ∈ U, _root_.TauCeti.idealAbscissaOfAbsConv K χ.toIdealArithmeticFunction < z.re := by
    intro z hz
    rw [hU, _root_.Set.mem_ofPred_eq] at hz
    exact _root_.lt_of_le_of_lt (by simpa using _root_.TauCeti.idealAbscissaOfAbsConv_le K hy) (by exact_mod_cast hz)
  have hsU : s ∈ U := by rw [hU, _root_.Set.mem_ofPred_eq]; exact hys
  have hUo : _root_.IsOpen U := by rw [hU]; exact _root_.isOpen_lt _root_.continuous_const _root_.Complex.continuous_re
  have hderiv : ∀ z ∈ U, _root_.HasDerivAt f
      (∑' pe : _root_.IsDedekindDomain.HeightOneSpectrum (𝓞 K) × ℕ,
        -(_root_.Complex.log (_root_.Ideal.absNorm pe.1.asIdeal : ℂ)
          * (χ pe.1.asIdeal / (_root_.Ideal.absNorm pe.1.asIdeal : ℂ) ^ z) ^ (pe.2 + 1))) z := by
    intro z hz
    rw [hf]
    exact χ.hasDerivAt_tsum_prime_pow (hmem z hz)
  have hdiff : _root_.DifferentiableOn ℂ f U := fun z hz ↦
    (hderiv z hz).differentiableAt.differentiableWithinAt
  have heq : _root_.Set.EqOn (_root_.Complex.exp ∘ f) (_root_.LSeries (_root_.TauCeti.normCoeff K χ.toIdealArithmeticFunction)) U := by
    intro z hz
    rw [_root_.Function.comp_apply, hf]
    exact χ.exp_tsum_prime_pow_eq_LSeries
      (_root_.TauCeti.summable_idealTerm_of_idealAbscissaOfAbsConv_lt_re K (hmem z hz))
  rw [← _root_.TauCeti.deriv_eq_logDeriv_of_eqOn_exp_comp hUo hdiff heq hsU, (hderiv s hsU).deriv]

end MultiplicativeIdealWeight

end TauCeti

end
end
