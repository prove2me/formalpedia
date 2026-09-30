-- Prove2me | solution 1 for TauCeti.primeCount_sub_mul_logIntegral_isLittleO
-- status  : ACCEPTED   (prove)
-- author  : @riccardo.brasca
-- created : 2026-09-29T22:03:17.603074+00:00
-- url     : https://prove2.me/submissions/9e6ecef7-bc7e-4933-8cbc-ea04a7ede37a

/- Transplanted from https://github.com/TauCetiProject/TauCeti at 948fe4751b1fe528b6d580c522ca5d743d47f185.
Original source copyright/license notices are retained below.
Generated exclusively from compiler declaration, command, and reference facts. -/
import Definitions.Def_TauCeti_Analysis_SpecialFunctions_LogIntegral
import Definitions.Def_TauCeti_NumberTheory_ArithmeticDirichletSeries_Counting
import Definitions.Def_TauCeti_NumberTheory_ArithmeticDirichletSeries_Weight
import Definitions.Def_TauCeti_Order_Northcott_Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.CharZero.Infinite
import Mathlib.Algebra.IsPrimePow
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Order
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.InvLog
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Set.Card
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.ZMod.Units
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.NumberTheory.AbelSummation
import Mathlib.NumberTheory.ArithmeticFunction.Defs
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
import Mathlib.NumberTheory.Padics.HeightOneSpectrum
import Mathlib.Order.Filter.AtTopBot.Finset
import Mathlib.Order.Northcott
import Mathlib.RingTheory.DedekindDomain.Factorization
import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.RingTheory.Ideal.Norm.AbsNorm
import Mathlib.RingTheory.Ideal.Quotient.HasFiniteQuotients
import Mathlib.RingTheory.Valuation.Discrete.IsDiscreteValuationRing
import Mathlib.Topology.Algebra.Order.Floor
import Mathlib.Topology.UniformSpace.Real
import Theorems.Thm_TauCeti_Real_isLittleO_integral_div_mul_log_sq
import Theorems.Thm_TauCeti_primeCount_sub_mul_logIntegral_eq

section
set_option autoImplicit true
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
/-!
# The logarithmic integral

This file defines the offset logarithmic integral `Li x = ∫ t in 2..x, (log t)⁻¹` and proves the
prime-number-theorem normalisation `Li x ~ x / log x` as `x → ∞`.

The lower endpoint is `2` rather than `0`: the integrand has a nonintegrable singularity at
`t = 1`, so the unshifted `li` exists only as a principal value, while every arithmetic
application compares a prime count with `Li`. The endpoint agrees with the one used by the
partial-summation identities for prime counts, so the two can be combined without a shift of
origin.

The asymptotic is proved from the exact identity
`Li x = x / log x - 2 / log 2 + ∫ t in 2..x, ((log t) ^ 2)⁻¹`,
the fundamental theorem of calculus applied to `t ↦ t / log t`, together with the estimate that
the remaining integral is `o (x / log x)`. Splitting that integral at `√x` bounds it by
`√x / (log 2) ^ 2 + 4 * x / (log x) ^ 2`, and both terms are `o (x / log x)`.

## Main declarations

* `TauCeti.Real.logIntegral` — the offset logarithmic integral.
* `TauCeti.Real.le_logIntegral` — the elementary lower bound `(x - 2) / log x ≤ Li x`.
* `TauCeti.Real.logIntegral_eq_div_log_sub_add` — the antiderivative identity above.
* `TauCeti.Real.logIntegral_isEquivalent_div_log` — `Li x ~ x / log x` at infinity, with the
  quotient form `TauCeti.Real.tendsto_logIntegral_mul_log_div_atTop`.
* `TauCeti.Real.tendsto_div_div_log_of_isLittleO_logIntegral` — an `o (x / log x)` error
  relative to `δ Li x` gives `f x / (x / log x) → δ`.
* `TauCeti.Real.isLittleO_integral_div_mul_log_sq` — for `f` interval integrable above `2` and of
  at most linear growth, `∫ t in 2..x, f t / (t * log t ^ 2)` is `o (x / log x)`.

The auxiliary bounds `TauCeti.Real.integral_inv_log_pow_le` and
`TauCeti.Real.le_integral_inv_log_pow` estimate `∫ t in a..b, ((log t) ^ n)⁻¹` by monotonicity of
the logarithm. They are stated for a general exponent because the identity above needs `n = 2`
while `Li` itself is the case `n = 1`.

## Roadmap role

This is the analytic half of Layer **6.2** of `TauCetiRoadmap/ArithmeticDirichletSeries/README.md`,
which asks for `Li` together with `Li(x) ∼ x/log x` on the way to the transfer
`ϑ(x) ∼ δx ⟹ π(x) ∼ δ Li(x)` that Layer 10.3 exports as `primeCount_asymptotic_of_primeTheta`.
The weighted-remainder estimate `isLittleO_integral_div_mul_log_sq` is the analytic input to that
transfer: it is what absorbs the integral produced by Abel summation.

## References

* H. Davenport, *Multiplicative Number Theory*, Chapter 1.
* G. Tenenbaum, *Introduction to Analytic and Probabilistic Number Theory*, Chapter I.

Mathlib's `Mathlib/NumberTheory/Chebyshev.lean` carries out this estimate for the rational
Chebyshev function, in `Chebyshev.integral_theta_div_log_sq_isLittleO`; the argument for a general
integrand below follows the same split into a bounded initial segment and a linearly bounded tail.
-/

 section

namespace TauCeti.Real

open Asymptotics Filter MeasureTheory Set
open scoped Topology

/-! ### Reciprocal powers of the logarithm -/











/-! ### The logarithmic integral -/











/-! ### The asymptotic `Li x ~ x / log x` -/













/-! ### A weighted remainder integral

The integral `∫ t in 2..x, f t / (t * log t ^ 2)` is what Abel summation leaves behind when a
logarithmically weighted counting function is converted into an unweighted one.  It is negligible
on the scale `x / log x` as soon as `f` grows at most linearly. -/

/-- **The Chebyshev scale `x / log x` diverges.**  Equivalently, a constant is `o (x / log x)`. -/
theorem tendsto_div_log_atTop : Tendsto (fun x : ℝ ↦ x / Real.log x) atTop atTop := by
  have hlog := Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero
  simp only [id_eq] at hlog
  have h : Tendsto (fun x : ℝ ↦ Real.log x / x) atTop (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ hlog ?_
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
    exact div_pos (Real.log_pos hx) (by linarith)
  exact h.inv_tendsto_nhdsGT_zero.congr fun x ↦ inv_div _ _

/-- A constant is `o (x / log x)`, because that scale diverges. -/
theorem isLittleO_const_div_log (c : ℝ) :
    (fun _ : ℝ ↦ c) =o[atTop] fun x : ℝ ↦ x / Real.log x :=
  isLittleO_const_left.mpr <| Or.inr <|
    (tendsto_abs_atTop_atTop.comp tendsto_div_log_atTop).congr fun _ ↦ (Real.norm_eq_abs _).symm











end TauCeti.Real

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
# Finite real-cutoff carriers for Northcott functions

This file packages the finite carrier selected by a real cutoff for a natural-valued Northcott
function, together with generic summatory functions over that carrier. The carrier depends only
on the integer part of the cutoff, and for a nonnegative cutoff it agrees with the one selected by
its natural floor.
-/

 section

namespace TauCeti

open Filter
open scoped Topology

variable {ι : Type*} (N : ι → ℕ) [Northcott N]





/-- An index belongs to `normLE N x` exactly when its `N`-value is at most the inclusive
real cutoff `x`. -/
@[simp, grind =]
theorem mem_normLE {i : ι} {x : ℝ} : i ∈ normLE N x ↔ (N i : ℝ) ≤ x := by
  simp [normLE]





/-- Increasing the real cutoff can only enlarge the finite carrier. -/
theorem normLE_mono : Monotone (normLE N) := fun _ _ hxy _ hi ↦
  mem_normLE N |>.mpr <| (mem_normLE N |>.mp hi).trans hxy











/-! ### Generic summatory functions -/























/-- A summatory function with nonnegative real weight is monotone in the cutoff. -/
theorem summatory_mono {w : ι → ℝ} (hw : ∀ i, 0 ≤ w i) : Monotone (summatory N w) :=
  fun _ _ hxy ↦ Finset.sum_le_sum_of_subset_of_nonneg (normLE_mono N hxy) fun i _ _ ↦ hw i









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
# Counting carriers for ideals and prime ideals

Every estimate in the arithmetic-Dirichlet-series roadmap counts objects whose absolute norm does
not exceed a *real* cutoff `x`, and always inclusively: an object of norm exactly `x` is counted.
This file fixes that convention once.

The common core is Mathlib's `Northcott` property: a function `N : ι → ℕ` is Northcott when each
set `{i | N i ≤ B}` is finite.  For such an `N`:

* `TauCeti.normLE N x` is the finite set of indices with `(N i : ℝ) ≤ x`;
* `TauCeti.summatory N w x` is the inclusive sum of a weight `w` over `TauCeti.normLE N x`.

Two instances of this core carry the arithmetic content, `TauCeti.idealsLE` for the nonzero
integral ideals of `𝓞 K` and `TauCeti.primesLE` for the height-one primes, with
`TauCeti.idealSummatory`, `TauCeti.primeSummatory`, and `TauCeti.primePowerSummatory` the associated
summatory functions.  The
weighted prime counts of the roadmap are the two named specializations
`TauCeti.primeTheta`, the logarithmically weighted count, and `TauCeti.primeCount`, the
unweighted one; both are restricted to a set `S` of height-one primes through `Set.indicator`,
so no decidability hypothesis is needed on `S`.

A prime-power ideal is `𝔭 ^ k` for a unique height-one prime `𝔭` and a unique `k ≥ 1`;
`TauCeti.primePowerBase` and `TauCeti.primePowerExponent` name that pair, and
`TauCeti.idealPrimePower_eq_of_base_eq_of_exponent_eq` records that it determines the ideal.  The
exponent is `1` exactly on the primes themselves, which is `TauCeti.primePowerExponent_eq_one_iff`;
`TauCeti.IdealPrimePower.ofPrime` is the resulting inclusion of the prime carrier into the
prime-power carrier, and `TauCeti.primePowerSummatory_eq_primeSummatory` uses it to read a
prime-power sum concentrated on the exponent-one part as a sum over primes.

`TauCeti.idealsLE_filter_dvd` identifies the ideals below a cutoff divisible by a fixed nonzero
ideal `P` with the multiples of `P`, and `TauCeti.idealSummatory_ite_dvd` reads the corresponding
part of a summatory function at the rescaled cutoff `x / N(P)`.

Two lemmas move a summatory function between the three carriers.
`TauCeti.idealSummatory_eq_primePowerSummatory` reads an ideal weight vanishing off the prime
powers as a prime-power weight, and `TauCeti.idealSummatory_eq_sum_range_normFiber` regroups an
ideal summatory function into the partial sum, over `n ≤ ⌊x⌋₊`, of the total mass on the norm
fibre at `n`; `TauCeti.idealSummatory_eq_sum_Icc_normCoeff` writes the same regrouping as a
partial sum of `TauCeti.normCoeff`.  Together they present a sum over prime powers as a partial
sum of an `ArithmeticFunction`, which is the shape a Tauberian theorem consumes.

For `0 ≤ x`, a real cutoff and its floor select the same indices, so
`TauCeti.normLE_eq_normLE_natFloor` and `TauCeti.summatory_eq_summatory_natFloor` convert between
the real and natural conventions. The small-cutoff cases are degenerate for a reason worth
recording: a nonzero ideal has absolute norm at least `1`, and a height-one prime at least `2`, so
`TauCeti.idealsLE_one` isolates the unit ideal and `TauCeti.primesLE_eq_empty_of_lt_two` empties the
prime carrier below `2`.

Modifying a weight on a finite set, or a prime set on a finite symmetric difference, changes a
summatory function by a quantity that is eventually the *constant* total discrepancy; this is
`TauCeti.eventually_summatory_sub_eq` and its two prime specializations. Layer 7 uses these to
show that finite changes do not affect a density. In the same spirit,
`TauCeti.primeTheta_isLittleO_of_finite` records that a finite set of primes contributes an
eventually constant amount to `ϑ_K`, hence `o(x)`: an exceptional set can be discarded from a
counting argument outright, not merely from a density. Its `ψ` companion is
`TauCeti.primePsi_isLittleO_of_finite`.

## Roadmap role

This is Layer **4** of `TauCetiRoadmap/ArithmeticDirichletSeries/README.md`: the finite cutoff
carriers of 4.1, the generic summatory functions on ideals, primes, and prime powers of 4.2, and the
weighted prime counts `primeTheta` and `primeCount` of 4.3. Layer 5 supplies the actual size
estimates for these counts, and consumes the prime base and exponent of a prime-power ideal to
fibre those estimates over the primes.

## References

* G. Tenenbaum, *Introduction to Analytic and Probabilistic Number Theory*, Chapters I--II.
* H. Davenport, *Multiplicative Number Theory*, Chapters 1 and 7.
* J. Neukirch, *Algebraic Number Theory*, Chapter VII.
-/

 section

namespace TauCeti

open _root_.Filter
open scoped _root_.nonZeroDivisors _root_.NumberField
open _root_.IsDedekindDomain

/-! ### Ideals and height-one primes of bounded absolute norm -/



variable (K : Type*) [Field K] [NumberField K]













variable {K}







/-! ### The prime base and the exponent of a prime-power ideal -/



























































variable (K)

/-! ### Summatory functions over ideals and over primes -/

































variable {K}

namespace MultiplicativeIdealWeight

variable (χ : MultiplicativeIdealWeight K)



end MultiplicativeIdealWeight

variable (K)









/-! ### The weighted prime counts -/





variable {K}
variable {S T : Set (HeightOneSpectrum (𝓞 K))} {x : ℝ}















/-- The logarithm of the absolute norm of a height-one prime is positive. -/
theorem log_absNorm_asIdeal_pos (v : HeightOneSpectrum (𝓞 K)) :
    0 < Real.log (Ideal.absNorm v.asIdeal : ℝ) :=
  Real.log_pos (by linarith [two_le_absNorm_asIdeal_real v])

/-- The logarithm of the absolute norm of a height-one prime is nonnegative. -/
theorem log_absNorm_asIdeal_nonneg (v : HeightOneSpectrum (𝓞 K)) :
    0 ≤ Real.log (Ideal.absNorm v.asIdeal : ℝ) :=
  (log_absNorm_asIdeal_pos v).le







/-- The logarithmically weighted prime count is monotone in the inclusive cutoff. -/
theorem primeTheta_mono (S : Set (HeightOneSpectrum (𝓞 K))) : Monotone (primeTheta K S) :=
  summatory_mono _ fun v ↦ Set.indicator_nonneg
    (fun v _ ↦ log_absNorm_asIdeal_nonneg v) v































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
# From the weighted prime count to the unweighted one

A prime-number-theorem argument delivers its conclusion for a *logarithmically weighted* count: a
Tauberian theorem applied to a logarithmic derivative sees the von Mangoldt coefficients, hence the
count `ψ` weighted by `log p` and taken over prime powers, and a separate elementary estimate for
the prime-power contribution passes from `ψ` to the count `ϑ` over primes alone.  The statement one
wants is about the *unweighted* count `π`.  This file carries out that last passage for the primes
of a number field, taking the asymptotic for `ϑ` as given: if `ϑ(x) = δx + o(x)`, then
`π(x) = δ Li(x) + o(x/log x)`, where `Li` is the offset logarithmic integral of
`TauCeti/Analysis/SpecialFunctions/LogIntegral.lean`.

The bridge is the exact Abel-summation identity
`TauCeti.primeCount_eq_primeTheta_div_log_add_integral` of Layer 6.1 together with the
antiderivative identity `TauCeti.Real.logIntegral_eq_div_log_sub_add` for `Li`.  Subtracting the two
cancels the main terms and leaves
`TauCeti.primeCount_sub_mul_logIntegral_eq`, an identity valid for every `x ≥ 2` and every `δ`,
whose three remaining summands are each `o (x / log x)`.

## Main results

* `TauCeti.primeCount_sub_mul_logIntegral_eq`: the exact identity
  `π(x) - δ Li(x) = (ϑ(x) - δx)/log x + ∫ t in 2..x, (ϑ(t) - δt)/(t log² t) + 2δ/log 2`.
* `TauCeti.primeCount_sub_mul_logIntegral_isLittleO`: the transfer itself, stated so that it covers
  the density `δ = 0` as well.
* `TauCeti.primeCount_asymptotic_of_primeTheta`: the quotient form `ϑ(x) ∼ δx ⟹ π(x) ∼ δ Li(x)`
  for `δ ≠ 0`, and `TauCeti.primeCount_isLittleO_logIntegral` for the zero-density case, where an
  asymptotic equivalence would be false and the correct statement is `π(x) = o(Li x)`.

## Roadmap role

This is Layer **6.2** of `TauCetiRoadmap/ArithmeticDirichletSeries/README.md`, which asks for the
transfer `ϑ(x) ∼ δx ⟹ π(x) ∼ δ Li(x)` "including the zero-density and `δ = 0` cases"; Layer 10.3
exports it as `primeCount_asymptotic_of_primeTheta`.  Nothing here uses an analytic continuation or
a nonvanishing statement: the hypothesis on `ϑ` is taken as given here, and Layer 10 supplies it.

## References

* H. Davenport, *Multiplicative Number Theory*, Chapter 1.
* G. Tenenbaum, *Introduction to Analytic and Probabilistic Number Theory*, Chapter I.2.

Mathlib's `Chebyshev.primeCounting_sub_theta_div_log_isBigO` performs the same partial-summation
step for the rational primes; the argument below follows it, and replaces its explicit Chebyshev
bound by the hypothesis on `ϑ`.
-/

 section

namespace TauCeti
end TauCeti
section TauCeti
open TauCeti

open Asymptotics Filter MeasureTheory
open scoped nonZeroDivisors NumberField
open IsDedekindDomain

variable {K : Type*} [Field K] [NumberField K] {S : Set (HeightOneSpectrum (𝓞 K))} {δ : ℝ}

/-- The error term `ϑ(t) - δ t` is interval integrable: `ϑ` is monotone and `t ↦ δ t` is
continuous. -/
theorem TauCeti.intervalIntegrable_primeTheta_sub_const_mul (S : _root_.Set (_root_.IsDedekindDomain.HeightOneSpectrum (𝓞 K)))
    (δ a b : ℝ) :
    _root_.IntervalIntegrable (fun t ↦ _root_.TauCeti.primeTheta K S t - δ * t) _root_.MeasureTheory.MeasureSpace.volume a b :=
  (_root_.TauCeti.primeTheta_mono S).intervalIntegrable.sub
    (_root_.Continuous.intervalIntegrable (by fun_prop) a b)



/-- **The transfer from `ϑ` to `π`.**  If the logarithmically weighted count of the primes of `S`
satisfies `ϑ(x) = δx + o(x)`, then the unweighted count satisfies `π(x) = δ Li(x) + o(x/log x)`.

Stated with an error term rather than as an equivalence, this covers `δ = 0` as well; the two
quotient forms are `TauCeti.primeCount_asymptotic_of_primeTheta` and
`TauCeti.primeCount_isLittleO_logIntegral`. -/
theorem solution
    (h : (fun x ↦ _root_.TauCeti.primeTheta K S x - δ * x) =o[_root_.Filter.atTop] _root_.id) :
    (fun x ↦ _root_.TauCeti.primeCount K S x - δ * _root_.TauCeti.Real.logIntegral x) =o[_root_.Filter.atTop] fun x : ℝ ↦ x / _root_.Real.log x := by
  have hboundary : (fun x ↦ (_root_.TauCeti.primeTheta K S x - δ * x) / _root_.Real.log x) =o[_root_.Filter.atTop]
      fun x : ℝ ↦ x / _root_.Real.log x := by
    simpa [_root_.div_eq_mul_inv] using
      h.mul_isBigO (_root_.Asymptotics.isBigO_refl (fun x : ℝ ↦ (_root_.Real.log x)⁻¹) _root_.Filter.atTop)
  have hintegral :
      (fun x ↦ ∫ t in (2 : ℝ)..x, (_root_.TauCeti.primeTheta K S t - δ * t) / (t * _root_.Real.log t ^ 2)) =o[_root_.Filter.atTop]
        fun x : ℝ ↦ x / _root_.Real.log x :=
    _root_.TauCeti.Real.isLittleO_integral_div_mul_log_sq
      (fun x _ ↦ _root_.TauCeti.intervalIntegrable_primeTheta_sub_const_mul S δ 2 x) h.isBigO
  have hconst := _root_.TauCeti.Real.isLittleO_const_div_log (2 * δ / _root_.Real.log 2)
  refine ((hboundary.add hintegral).add hconst).congr' ?_ _root_.Filter.EventuallyEq.rfl
  filter_upwards [_root_.Filter.eventually_ge_atTop (2 : ℝ)] with x hx
  exact (_root_.TauCeti.primeCount_sub_mul_logIntegral_eq S δ hx).symm





end TauCeti

end
end
