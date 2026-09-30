-- Prove2me | solution 1 for TauCeti.tendsto_log_dedekindZeta_re_sub_log_one_div_sub_one
-- status  : ACCEPTED   (prove)
-- author  : @riccardo.brasca
-- created : 2026-09-29T22:01:33.357312+00:00
-- url     : https://prove2.me/submissions/ac7be2b7-0858-445e-94e4-d22dde684827

/- Transplanted from https://github.com/TauCetiProject/TauCeti at 948fe4751b1fe528b6d580c522ca5d743d47f185.
Original source copyright/license notices are retained below.
Generated exclusively from compiler declaration, command, and reference facts. -/
import Mathlib.Algebra.Algebra.Subalgebra.Basic
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.CharP.Basic
import Mathlib.Algebra.CharZero.Infinite
import Mathlib.Algebra.IsPrimePow
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Ring.Subgroup
import Mathlib.Algebra.Ring.Subring.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Order
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Set.Card
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.ZMod.Units
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.FieldTheory.KummerPolynomial
import Mathlib.LinearAlgebra.Pi
import Mathlib.NumberTheory.ArithmeticFunction.Defs
import Mathlib.NumberTheory.ArithmeticFunction.LFunction
import Mathlib.NumberTheory.EulerProduct.ExpLog
import Mathlib.NumberTheory.LSeries.Convergence
import Mathlib.NumberTheory.LSeries.Convolution
import Mathlib.NumberTheory.LSeries.SumCoeff
import Mathlib.NumberTheory.LegendreSymbol.Basic
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
import Mathlib.NumberTheory.NumberField.DedekindZeta
import Mathlib.NumberTheory.NumberField.DirichletDensity
import Mathlib.NumberTheory.NumberField.Ideal.Asymptotics
import Mathlib.NumberTheory.NumberField.Ideal.Basic
import Mathlib.NumberTheory.Padics.HeightOneSpectrum
import Mathlib.NumberTheory.RamificationInertia.Galois
import Mathlib.NumberTheory.RamificationInertia.Unramified
import Mathlib.NumberTheory.ZetaValues
import Mathlib.Order.Filter.AtTopBot.Finset
import Mathlib.Order.Northcott
import Mathlib.RingTheory.ClassGroup.Basic
import Mathlib.RingTheory.DedekindDomain.Factorization
import Mathlib.RingTheory.DedekindDomain.Ideal.Basic
import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
import Mathlib.RingTheory.Frobenius
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.RingTheory.Ideal.Int
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.RingTheory.Ideal.Norm.AbsNorm
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.RingTheory.Ideal.Over
import Mathlib.RingTheory.Ideal.Quotient.HasFiniteQuotients
import Mathlib.RingTheory.Ideal.Span
import Mathlib.RingTheory.Localization.Basic
import Mathlib.RingTheory.RamificationInertia.Basic
import Mathlib.RingTheory.RamificationInertia.Inertia
import Mathlib.RingTheory.RamificationInertia.Ramification
import Mathlib.RingTheory.UniqueFactorizationDomain.Finite
import Mathlib.RingTheory.Unramified.Locus
import Mathlib.RingTheory.Valuation.Discrete.IsDiscreteValuationRing
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Topology.Algebra.Order.Floor
import Mathlib.Topology.UniformSpace.Real
import Theorems.Thm_TauCeti_dedekindZeta_ofReal_eq_exp_tsum_neg_log_one_sub

section
set_option autoImplicit true
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
/-!
# The real Euler product of the Dedekind zeta function in exponential form

For real `s > 1`, every local ratio `x = N(𝔭) ^ (-s)` of a height-one prime lies in `(0, 1/2]`,
because `N(𝔭) ≥ 2`. The principal logarithm of each Euler factor is then the real number
`-log (1 - x)`, and the exponential form
`TauCeti.MultiplicativeIdealWeight.exp_tsum_neg_log_one_sub_eq_LSeries` of the Euler product,
specialized to the trivial weight, becomes a statement about real numbers: `ζ_K(s)` is the
exponential of the convergent real sum `∑_𝔭 -log (1 - N(𝔭) ^ (-s))`. In particular `ζ_K(s)` is a
positive real number, and that sum is its real logarithm.

## Main results

* `IsDedekindDomain.HeightOneSpectrum.absNorm_rpow_neg_le_half`: `N(𝔭) ^ (-s) ≤ 1/2`
  for `1 ≤ s`.
* `TauCeti.summable_neg_log_one_sub_absNorm_rpow`: `∑_𝔭 -log (1 - N(𝔭) ^ (-s))` converges for
  `1 < s`.
* `TauCeti.dedekindZeta_ofReal_eq_exp_tsum_neg_log_one_sub`: for real `s > 1`, `ζ_K(s)` is the
  exponential of that real sum.
* `TauCeti.dedekindZeta_re_eq_exp` and `TauCeti.dedekindZeta_re_pos`: the same for the real part,
  which is therefore positive.
* `TauCeti.log_dedekindZeta_re_eq_tsum_neg_log_one_sub`: that real sum is the real logarithm of
  `ζ_K(s)`.

## References

* The real logarithmic identity also appears, under the same name, in the
  Birkbeck–Brasca Chebotarev density project, <https://github.com/CBirkbeck/chebotarev-density>
  (Apache-2.0), commit `8575c9df1ae0a61120ab5c964c7911414254bec7`, file
  `CebotarevDensity/Density.lean`, where it is proved from `Real.hasProd_of_hasSum_log` and the
  product formula. It is derived here instead from TauCeti's exponential Euler product
  `TauCeti.MultiplicativeIdealWeight.exp_tsum_neg_log_one_sub_eq_LSeries`.
-/

 section

open _root_.IsDedekindDomain _root_.NumberField

namespace IsDedekindDomain.HeightOneSpectrum

variable {K : Type*} [Field K] [NumberField K]



end IsDedekindDomain.HeightOneSpectrum

namespace TauCeti

variable {K : Type*} [Field K] [NumberField K]





/-- For real `s > 1`, the real part of `ζ_K(s)` is the exponential of `∑_𝔭 -log (1 - N(𝔭) ^ (-s))`.
-/
theorem dedekindZeta_re_eq_exp {s : ℝ} (hs : 1 < s) :
    (dedekindZeta K s).re = Real.exp (∑' P : HeightOneSpectrum (𝓞 K),
      -Real.log (1 - (Ideal.absNorm P.asIdeal : ℝ) ^ (-s))) := by
  rw [dedekindZeta_ofReal_eq_exp_tsum_neg_log_one_sub hs, Complex.ofReal_re]



/-- For real `s > 1`, the real part of `ζ_K(s)` is positive. -/
theorem dedekindZeta_re_pos {s : ℝ} (hs : 1 < s) : 0 < (dedekindZeta K s).re := by
  rw [dedekindZeta_re_eq_exp hs]
  exact Real.exp_pos _

end TauCeti

end
end

section
set_option autoImplicit true
namespace TauCeti
end TauCeti
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
/-!
# The all-prime Dirichlet sum is `log (1 / (s - 1)) + O(1)`

For a number field `K`, write `P(s) = ∑_𝔭 N(𝔭) ^ (-s)` for the sum over all height-one primes of
`𝓞 K`, which is `NumberField.Set.primeIdealZetaSum Set.univ s`. This file proves that
`P(s) = log (1 / (s - 1)) + O(1)` as `s → 1⁺`, and hence that Mathlib's ratio-normalized
`NumberField.Set.HasDirichletDensity` agrees with the logarithmically normalized density.

The proof has two inputs, and neither suffices alone.

* **The Euler product.** For real `s > 1`, `log ζ_K(s)` is the convergent sum
  `∑_𝔭 -log (1 - N(𝔭) ^ (-s))`, by `TauCeti.log_dedekindZeta_re_eq_tsum_neg_log_one_sub`.
  The higher-prime-power tail theorem
  `TauCeti.abs_tsum_neg_log_one_sub_sub_primeIdealZetaSum_le` bounds the difference from `P(s)`
  by `2 [K : ℚ]`, uniformly for `s > 1`.
* **The residue.** Mathlib's class number formula
  `NumberField.tendsto_sub_one_mul_dedekindZeta_nhdsGT` says that `(s - 1) ζ_K(s)` tends to the
  positive residue as `s → 1⁺`, so `log ζ_K(s) - log (1 / (s - 1))` tends to its logarithm.

## Main results

* `TauCeti.primeIdealZetaSum_univ_le_log_dedekindZeta_re` and
  `TauCeti.log_dedekindZeta_re_le_primeIdealZetaSum_univ_add`: the two-sided comparison of
  `log ζ_K(s)` with `P(s)`, with error at most `2 [K : ℚ]`.
* `TauCeti.tendsto_log_dedekindZeta_re_sub_log_one_div_sub_one`: `log ζ_K(s) - log (1 / (s - 1))`
  tends to the logarithm of the residue.
* `TauCeti.primeIdealZetaSum_univ_sub_log_one_div_sub_one_isBigO`:
  `P(s) - log (1 / (s - 1)) = O(1)` as `s → 1⁺`.
* `TauCeti.tendsto_primeIdealZetaSum_univ_atTop`: `P(s) → ∞` as `s → 1⁺`.
* `TauCeti.tendsto_primeIdealZetaSum_univ_div_log_one_div_sub_one`:
  `P(s) / log (1 / (s - 1)) → 1` as `s → 1⁺`.
* `NumberField.Set.hasDirichletDensity_iff_tendsto_div_log_one_div_sub_one`: a set of primes has
  Dirichlet density `δ` exactly when `P_S(s) / log (1 / (s - 1)) → δ`.
* `NumberField.Set.ofReal_primeIdealZetaSum`: `P_S(t)`, cast to `ℂ`, is the complex sum over all
  primes of the indicator of `S` against `N(𝔭) ^ (-t)`.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter VII, §13.
* J.-P. Serre, *A Course in Arithmetic*, Chapter VI, §4.1.
* The same argument (Sharifi, *Algebraic Number Theory*, 7.1.12) is formalized in the
  Birkbeck–Brasca Chebotarev density project, <https://github.com/CBirkbeck/chebotarev-density>
  (Apache-2.0), commit `8575c9df1ae0a61120ab5c964c7911414254bec7`, file
  `CebotarevDensity/Density.lean`: `primeIdealZetaSum_univ_tendsto_log` and
  `primeIdealZetaSum_univ_tendsto_atTop`, closed there by the helpers of
  `CebotarevDensity/ForMathlib/LogOneDivSubOne.lean` that `Real.tendsto_log_one_div_sub_atTop`
  and `TauCeti.tendsto_div_nhds_one_of_le_add_const_of_sub_const_le` adapt. This file follows
  its outline (Euler-product logarithm, bounded higher-prime-power contribution, simple pole),
  over `HeightOneSpectrum` rather than the nonzero prime ideals of `𝓞 K`. It derives the
  logarithmic form of the Euler product from
  `TauCeti.MultiplicativeIdealWeight.exp_tsum_neg_log_one_sub_eq_LSeries` and uses the explicit
  higher-prime-power bound from
  `TauCeti.abs_tsum_neg_log_one_sub_sub_primeIdealZetaSum_le`.
-/

 section

open _root_.Filter _root_.Asymptotics _root_.IsDedekindDomain _root_.NumberField
open scoped _root_.Topology

namespace TauCeti
end TauCeti
section TauCeti
open TauCeti

variable {K : Type*} [Field K] [NumberField K]





/-! ### The residue and the logarithmic normalization -/

/-- **`log ζ_K(s) = log (1 / (s - 1)) + log κ_K + o(1)`.** As `s → 1⁺`, the difference between the
real logarithm of `ζ_K(s)` and `log (1 / (s - 1))` tends to the logarithm of the residue
`NumberField.dedekindZeta_residue K`. This is the logarithm of Mathlib's class number formula
`NumberField.tendsto_sub_one_mul_dedekindZeta_nhdsGT`. -/
theorem solution :
    _root_.Filter.Tendsto (fun s : ℝ ↦ _root_.Real.log (_root_.NumberField.dedekindZeta K s).re - _root_.Real.log (1 / (s - 1))) (𝓝[>] 1)
      (𝓝 (_root_.Real.log (_root_.NumberField.dedekindZeta_residue K))) := by
  have hre : _root_.Filter.Tendsto (fun s : ℝ ↦ (s - 1) * (_root_.NumberField.dedekindZeta K s).re) (𝓝[>] 1)
      (𝓝 (_root_.NumberField.dedekindZeta_residue K)) := by
    have h := (Complex.continuous_re.tendsto _).comp (_root_.NumberField.tendsto_sub_one_mul_dedekindZeta_nhdsGT K)
    refine (_root_.Complex.ofReal_re (_root_.NumberField.dedekindZeta_residue K) ▸ h).congr fun s ↦ ?_
    simp only [_root_.Function.comp_apply]
    rw [← _root_.Complex.ofReal_one, ← _root_.Complex.ofReal_sub, _root_.Complex.re_ofReal_mul]
  refine (hre.log (_root_.NumberField.dedekindZeta_residue_ne_zero K)).congr' ?_
  filter_upwards [_root_.self_mem_nhdsWithin] with s hs
  have hs' : 0 < s - 1 := sub_pos.mpr hs
  rw [_root_.Real.log_mul hs'.ne' (_root_.TauCeti.dedekindZeta_re_pos hs).ne', _root_.one_div, _root_.Real.log_inv]
  ring









end TauCeti

namespace NumberField.Set
end NumberField.Set
section NumberField.Set
open NumberField NumberField.Set

open _root_.TauCeti

variable {K : Type*} [Field K] [NumberField K]





end NumberField.Set

end
end
