-- Prove2me | solution 1 for OddOrder.Peterfalvi.S15.CharacterDegreeCore.analyticEstimate_eta_core
-- status  : ACCEPTED   (prove)
-- author  : @burkh4rt
-- created : 2026-11-12T17:03:16.444991+00:00
-- url     : https://prove2.me/submissions/e6d408e5-785e-42d8-8633-2763185b3918

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/Peterfalvi/S15_SAndT_Setup/Machinery135.lean
--   OddOrder/Peterfalvi/S15_SAndT_Setup/DegreesFirstSplit.lean
--   OddOrder/Peterfalvi/S15_SAndT_Setup/CountingLayer.lean
--   OddOrder/Peterfalvi/S15_SAndT_Setup/Canonicalization.lean
--   OddOrder/Peterfalvi/S15_SAndT_Setup/NormEstimates.lean
--   OddOrder/Peterfalvi/S15_CaseBEndgameSupply/Eta10HCorrection.lean
--   OddOrder/Peterfalvi/S15_CaseBEndgameSupply/Eta10Correction.lean
--   OddOrder/Peterfalvi/S15_CaseBEndgameSupply/AnalyticRelayer.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Theorems.Thm_OddOrder_Algebra_exists_nat_sum_normSq_of_mem_ZIrr_of_cyclicClosed
import Theorems.Thm_OddOrder_Peterfalvi_S15_Hypothesis_exists_caseB_data_eta10_T_core
import Theorems.Thm_OddOrder_Peterfalvi_S15_CharacterDegreeCore_exists_caseB_data_eta10_H_core
import Theorems.Thm_OddOrder_Peterfalvi_S15_Hypothesis_sum_univ_split
import Theorems.Thm_OddOrder_Peterfalvi_S15_Hypothesis_G0Finset_cyclicClosed

-- ===== OddOrder/Peterfalvi/S15_SAndT_Setup/Machinery135.lean =====
namespace OddOrder.Peterfalvi.S15

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

open OddOrder.Isaacs

open scoped Pointwise

variable {G : Type*} [Group G]

/-- **Self inner-sum as a real squared-norm sum** (general `ClassFunction` identity).

For any class function `α : H → ℂ`, the unscaled self inner sum `Σ_g α(g)·conj(α(g))` equals the
real sum of squared norms `Σ_g ‖α(g)‖²` cast to `ℂ`.  This is the bridge between the abstract
`ClassFunction.innerSum`/`inner` API and the concrete `Σ |α(g)|²` quantities of Peterfalvi's norm
estimates (13.6)–(13.10); combined with `Σ_{H#} = Σ_H − |α(1)|²` it converts every Dade-norm
inequality into an elementary squared-norm sum.  A general fact for any finite group `H`. -/
theorem innerSum_self_eq_sum_normSq {H : Type*} [Group H] [Fintype H]
    (α : ClassFunction H ℂ) :
    ClassFunction.innerSum α α = ((∑ g : H, ‖α g‖ ^ 2 : ℝ) : ℂ) := by
  rw [ClassFunction.innerSum, Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [← starRingEnd_apply, RCLike.mul_conj]
  norm_cast

/-- **Parseval identity for class functions** (general): `Σ_g ‖α(g)‖² = |H| · ⟨α, α⟩`.

The full squared-norm sum equals `|H|` times the normalized self inner product `⟨α,α⟩ = ‖α‖²`.
Combined with `Σ_{H#} = Σ_H − ‖α(1)‖²` this is precisely the Parseval relation `s + d² = |H|·n`
consumed by `caseB_eta_norm_core` (the (13.7) core): it lets the cascade read off `s = ∑_{H#}|α|²`
from the abstract inner product `n = ⟨α,α⟩`.  Immediate from `innerSum_self_eq_sum_normSq` and
`ClassFunction.card_mul_inner`. -/
theorem sum_normSq_eq_card_mul_inner {H : Type*} [Group H] [Fintype H]
    [Invertible (Nat.card H : ℂ)] (α : ClassFunction H ℂ) :
    ((∑ g : H, ‖α g‖ ^ 2 : ℝ) : ℂ) = (Nat.card H : ℂ) * ClassFunction.inner α α := by
  rw [← innerSum_self_eq_sum_normSq, ClassFunction.card_mul_inner]

/-- **Parseval expansion of a real-scalar linear combination** (the algebraic core of Peterfalvi
(13.5.b)).  For complex functions `f, g` on a finite index set and a real scalar `κ`,
`∑‖κ·f + g‖² = κ²∑‖f‖² + 2κ·Re(∑ f·ḡ) + ∑‖g‖²`.  In (13.5.b) this is applied with `κ = a/‖ζ₁‖²`,
`f = ζ₁`, `g = α` on `H#`; together with the (13.5) sum facts `∑_{H#}|ζ₁|² = |S|‖ζ₁‖² − ζ₁(1)²` and
`∑_{H#} ζ₁ᾱ = −ζ₁(1)α(1)` it yields the (13.5.b) norm decomposition consumed by
`caseB_lambda_norm_core`
(13.6) and `caseB_eta01_norm_core` (13.8). -/
theorem sum_normSq_real_smul_add {ι : Type*} (s : Finset ι) (κ : ℝ) (f g : ι → ℂ) :
    (∑ x ∈ s, ‖(κ : ℂ) * f x + g x‖ ^ 2)
      = κ ^ 2 * (∑ x ∈ s, ‖f x‖ ^ 2)
        + 2 * κ * (∑ x ∈ s, f x * (starRingEnd ℂ) (g x)).re
        + (∑ x ∈ s, ‖g x‖ ^ 2) := by
  have hpt : ∀ x ∈ s, ‖(κ : ℂ) * f x + g x‖ ^ 2
      = κ ^ 2 * ‖f x‖ ^ 2 + 2 * κ * (f x * (starRingEnd ℂ) (g x)).re + ‖g x‖ ^ 2 := by
    intro x _
    rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq,
      Complex.normSq_add, Complex.normSq_mul, Complex.normSq_ofReal]
    rw [show ((κ : ℂ) * f x) * (starRingEnd ℂ) (g x) = (κ : ℂ) * (f x * (starRingEnd ℂ) (g x)) by
        ring,
      Complex.re_ofReal_mul]
    ring
  rw [Finset.sum_congr rfl hpt, Finset.sum_add_distrib, Finset.sum_add_distrib,
    ← Finset.mul_sum, ← Finset.mul_sum, ← Complex.re_sum]

open scoped Classical in
/-- **Peterfalvi (13.5), `ζ₁`-norm sum** (the (13.5.b) `firstTerm`): for a function `ζ` on `S`
vanishing outside the subgroup `H ≤ S`, the squared-norm sum over `H# = H ∖ {1}` equals the full sum
over `S` minus the value at `1`.  In (13.5) `ζ = ζ₁` vanishes on `S − H` (induced from `H`, with `P`
off the kernels), so combined with Parseval `∑_{x∈S}‖ζ₁‖² = |S|·‖ζ₁‖²`
(`sum_normSq_eq_card_mul_inner`)
this gives `∑_{H#}|ζ₁|² = |S|‖ζ₁‖² − ζ₁(1)²`, the `firstTerm` consumed by `caseB_lambda_norm_core`
(13.6) and `caseB_eta01_norm_core` (13.8). -/
theorem sum_normSq_sharp_eq_total_sub_one {S : Type*} [Group S] [Fintype S]
    (H : Subgroup S) (ζ : S → ℂ) (hvanish : ∀ x : S, x ∉ H → ζ x = 0) :
    ∑ x ∈ (Finset.univ.filter (· ∈ H)).erase (1 : S), ‖ζ x‖ ^ 2
      = (∑ x : S, ‖ζ x‖ ^ 2) - ‖ζ 1‖ ^ 2 := by
  have hHfull : (∑ x : S, ‖ζ x‖ ^ 2) = ∑ x ∈ Finset.univ.filter (· ∈ H), ‖ζ x‖ ^ 2 := by
    refine (Finset.sum_subset (Finset.subset_univ _) ?_).symm
    intro x _ hx
    rw [hvanish x (by simpa using hx)]; simp
  rw [hHfull, ← Finset.sum_erase_add (Finset.univ.filter (· ∈ H)) (fun x => ‖ζ x‖ ^ 2)
    (Finset.mem_filter.mpr ⟨Finset.mem_univ 1, H.one_mem⟩)]
  ring

open scoped Classical in
/-- **Peterfalvi (13.5), cross-term sum** (the (13.5.b) `−2a ζ₁(1)α(1)/‖ζ₁‖²` term): when the inner
sum `∑_{x∈H} ζ₁(x)·conj(α(x))` over the subgroup `H` vanishes — which holds in (13.5) because
`Res_H ζ₁` is a sum of characters with `P` *off* their kernels while every component of `α` has `P`
*in* its kernel (orthogonal constituents) — the sum over `H# = H ∖ {1}` collapses to the single
identity term: `∑_{H#} ζ₁·ᾱ = −ζ₁(1)·conj(α(1))`.  Supplies the cross term of the (13.5.b)
decomposition `sum_normSq_real_smul_add` (with `f = ζ₁`, `g = α`). -/
theorem sum_mul_conj_sharp_eq_neg_of_inner_zero {S : Type*} [Group S] [Fintype S]
    (H : Subgroup S) (ζ α : S → ℂ)
    (hinner : ∑ x ∈ Finset.univ.filter (· ∈ H), ζ x * (starRingEnd ℂ) (α x) = 0) :
    ∑ x ∈ (Finset.univ.filter (· ∈ H)).erase 1, ζ x * (starRingEnd ℂ) (α x)
      = -(ζ 1 * (starRingEnd ℂ) (α 1)) := by
  rw [← Finset.sum_erase_add (Finset.univ.filter (· ∈ H))
    (fun x => ζ x * (starRingEnd ℂ) (α x))
    (Finset.mem_filter.mpr ⟨Finset.mem_univ 1, H.one_mem⟩)] at hinner
  exact eq_neg_of_add_eq_zero_left hinner

open scoped Classical in
/-- **Peterfalvi (13.5.b), norm-sum decomposition**: assembling the (13.5.a) point formula
`χ = κ·ζ₁ + α` (on `H#`, here the hypothesis `hχ`) with Parseval (`sum_normSq_real_smul_add`),
the `ζ₁`-vanishing fact (`sum_normSq_sharp_eq_total_sub_one`, needs `hvanish`) and the cross-term
fact (`sum_mul_conj_sharp_eq_neg_of_inner_zero`, needs `hinner` = `(Res_H ζ₁, α) = 0`) gives

  `∑_{H#}|χ|² = κ²(∑_S|ζ₁|² − ζ₁(1)²) − 2κ·Re(ζ₁(1)·conj α(1)) + ∑_{H#}|α|²`.

Specialised with `κ = a/‖ζ₁‖²` and the norm identity `∑_S|ζ₁|² = |S|‖ζ₁‖²`, this is the textbook
(13.5.b) `(a²/‖ζ₁‖²)(|S| − ζ₁(1)²/‖ζ₁‖²) − 2a·ζ₁(1)α(1)/‖ζ₁‖² + ∑_{H#}|α|²`, the decomposition
consumed by `caseB_lambda_norm_core` (13.6) / `caseB_eta_norm_core` (13.7) /
`caseB_eta01_norm_core` (13.8).  Generic in `(ζ₁, α, χ, κ)`; the three character-theoretic
hypotheses (`hvanish`, `hinner`, `hχ`) are discharged per-case from the (13.5.a) data. -/
theorem sum_normSq_sharp_chi_decomp {S : Type*} [Group S] [Fintype S]
    (H : Subgroup S) (ζ α χ : S → ℂ) (κ : ℝ)
    (hvanish : ∀ x : S, x ∉ H → ζ x = 0)
    (hinner : ∑ x ∈ Finset.univ.filter (· ∈ H), ζ x * (starRingEnd ℂ) (α x) = 0)
    (hχ : ∀ x ∈ (Finset.univ.filter (· ∈ H)).erase 1, χ x = (κ : ℂ) * ζ x + α x) :
    ∑ x ∈ (Finset.univ.filter (· ∈ H)).erase 1, ‖χ x‖ ^ 2
      = κ ^ 2 * ((∑ x : S, ‖ζ x‖ ^ 2) - ‖ζ 1‖ ^ 2)
        - 2 * κ * (ζ 1 * (starRingEnd ℂ) (α 1)).re
        + ∑ x ∈ (Finset.univ.filter (· ∈ H)).erase 1, ‖α x‖ ^ 2 := by
  have hstep : ∑ x ∈ (Finset.univ.filter (· ∈ H)).erase 1, ‖χ x‖ ^ 2
      = ∑ x ∈ (Finset.univ.filter (· ∈ H)).erase 1, ‖(κ : ℂ) * ζ x + α x‖ ^ 2 :=
    Finset.sum_congr rfl (fun x hx => by rw [hχ x hx])
  rw [hstep, sum_normSq_real_smul_add, sum_normSq_sharp_eq_total_sub_one H ζ hvanish,
    sum_mul_conj_sharp_eq_neg_of_inner_zero H ζ α hinner, Complex.neg_re]
  ring

/-- **Key nonnegativity of Peterfalvi (13.6)**: the quadratic correction term is `≥ 0`.

In (13.6) the inflation degree satisfies `α(1) = q·b` for an integer `b`, and the bound reduces to
`(|P|−1)·α(1)² − 2·λ(1)·α(1) = q²·((|P|−1)·b² − 2u·b) ≥ 0`, using `u ≤ (|P|−1)/2` from (13.2.c).
This is exactly that nonnegativity `0 ≤ (|P|−1)·b² − 2u·b` (here `Pm1 = |P| − 1`), pure
ℤ-arithmetic:
`(|P|−1)b² − 2ub = (|P|−1−2u)·b² + 2u·b(b−1)`, both summands `≥ 0` (the first by `2u ≤ |P|−1`, the
second since consecutive integers `b(b−1) ≥ 0`).  Carrier-free core of the (13.6) estimate. -/
theorem caseB_quadratic_nonneg {Pm1 u : ℕ} (hu : 2 * u ≤ Pm1) (b : ℤ) :
    0 ≤ (Pm1 : ℤ) * b ^ 2 - 2 * (u : ℤ) * b := by
  have h2u : (2 * u : ℤ) ≤ (Pm1 : ℤ) := by exact_mod_cast hu
  have hb : 0 ≤ b * (b - 1) := by
    by_cases h : 1 ≤ b
    · exact mul_nonneg (by linarith) (by linarith)
    · push Not at h
      calc 0 ≤ (-b) * (-(b - 1)) := mul_nonneg (by omega) (by omega)
        _ = b * (b - 1) := by ring
  nlinarith [mul_nonneg (by linarith : (0 : ℤ) ≤ (Pm1 : ℤ) - 2 * u) (sq_nonneg b),
    mul_nonneg (by positivity : (0 : ℤ) ≤ 2 * (u : ℤ)) hb]

/-- **Arithmetic core of Peterfalvi (13.7)**: the norm lower bound `∑_{x∈H#}|η₁₀(x)|² ≥ |H#|`.

In (13.7), for `α = η₁₀` on `H#` with `α(1) = d` and squared norm `‖α‖² = n`, one has:
* the Parseval relation `s + d² = |H|·n` where `s = ∑_{H#}|α|²` (from `∑_{x∈H}|α|² = |H|‖α‖²`);
* the inflation bound `(|P|−1)·d² ≤ s` (Peterfalvi (13.5.c));
* `n ≥ 1` (`α` a nonzero virtual character), `|P| ≥ 2`, and — `H` being abelian — `n = 1 ⟹ d² = 1`.

Then `s ≥ |H| − 1 = |H#|`.  Carrier-free arithmetic core (`H, P, d, n, s` abstract naturals; the
character-theoretic inputs are supplied by the cascade).  Proof: `n = 1` gives `s = |H| − 1`
directly; for `n ≥ 2`, multiplying through by `|P|` reduces to `|P|(|H|−1) ≤ |H|n(|P|−1)`
(true since `n, |P| ≥ 2`) together with `|P|·d² ≤ |H|n` (from the inflation bound). -/
theorem caseB_eta_norm_core {H P d n s : ℕ}
    (hP : 2 ≤ P) (hn : 1 ≤ n) (hParseval : s + d ^ 2 = H * n)
    (hInflation : (P - 1) * d ^ 2 ≤ s) (habelian : n = 1 → d ^ 2 = 1) :
    H - 1 ≤ s := by
  by_cases hn2 : 2 ≤ n
  · -- `n ≥ 2`
    have hPos : 1 ≤ P := by omega
    have hcast_infl : ((P : ℤ) - 1) * (d : ℤ) ^ 2 ≤ (s : ℤ) := by
      have h : ((P - 1 : ℕ) : ℤ) * (d : ℤ) ^ 2 ≤ (s : ℤ) := by exact_mod_cast hInflation
      rwa [Nat.cast_sub hPos, Nat.cast_one] at h
    have hPar : (s : ℤ) + (d : ℤ) ^ 2 = (H : ℤ) * n := by exact_mod_cast hParseval
    have hH : (0 : ℤ) ≤ (H : ℤ) := by positivity
    have hn2' : (2 : ℤ) ≤ (n : ℤ) := by exact_mod_cast hn2
    have hP2' : (2 : ℤ) ≤ (P : ℤ) := by exact_mod_cast hP
    have hPd2 : (P : ℤ) * (d : ℤ) ^ 2 ≤ (H : ℤ) * n := by nlinarith [hcast_infl, hPar]
    have hkey : (P : ℤ) * ((H : ℤ) - 1) ≤ (H : ℤ) * n * ((P : ℤ) - 1) := by
      nlinarith [mul_nonneg (mul_nonneg hH (by linarith : (0:ℤ) ≤ (n:ℤ) - 2))
          (by linarith : (0:ℤ) ≤ (P:ℤ) - 1),
        mul_nonneg hH (by linarith : (0:ℤ) ≤ (P:ℤ) - 2), hP2']
    have hs_eq : (s : ℤ) = (H : ℤ) * n - (d : ℤ) ^ 2 := by linarith [hPar]
    have hPpos : (0 : ℤ) < (P : ℤ) := by linarith
    have hmul : (P : ℤ) * ((H : ℤ) - 1) ≤ (P : ℤ) * (s : ℤ) := by
      rw [hs_eq]; nlinarith [hkey, hPd2]
    have hfin : (H : ℤ) - 1 ≤ (s : ℤ) := le_of_mul_le_mul_left hmul hPpos
    omega
  · -- `n = 1`
    have hn_eq : n = 1 := by omega
    subst hn_eq
    rw [mul_one] at hParseval
    have hd : d ^ 2 = 1 := habelian rfl
    omega

/-- **Peterfalvi (13.7), character-theoretic bound**: the norm lower bound
`∑_{x∈H#}|η₁₀(x)|² ≥ |H#|`, assembled from the (13.5) machinery.

For `χ = η₁₀` the (13.5) hypothesis holds with `a = 0`, so the (13.5.a) point formula collapses to
`η₁₀ = α` on `H#` (no `ζ₁` term — `hχ`); hence `∑_{H#}|η₁₀|² = ∑_{H#}|α|²`.  The character-theoretic
sum is an integer `s` (`hs`: `∑_{H#}|α|² = s`, since `∑_{x∈H}|α|² = |H|‖α‖²` is an integer and
`α(1) ∈ ℤ`), and the arithmetic core `caseB_eta_norm_core` gives `s ≥ |H| − 1 = |H#|`.  Bridges the
nat-valued core to the real-valued cascade input consumed by the (13.10) analytic inequality.
Honest hypotheses: `hχ` the (13.5.a) `a = 0` point formula; `hs` integrality; `hParseval`
`s + α(1)² = |H|‖α‖²`; `hInflation` (13.5.c); `habelian` (13.2.b, `H` abelian + `α` faithful). -/
theorem caseB_eta_norm_bound {S : Type*} [Group S] [Finite S]
    (α χ : S → ℂ) (A : Finset S) {Hcard P d n s : ℕ}
    (hH : 1 ≤ Hcard)
    (hχ : ∀ x ∈ A, χ x = α x)
    (hs : ∑ x ∈ A, ‖α x‖ ^ 2 = (s : ℝ))
    (hP : 2 ≤ P) (hn : 1 ≤ n) (hParseval : s + d ^ 2 = Hcard * n)
    (hInflation : (P - 1) * d ^ 2 ≤ s) (habelian : n = 1 → d ^ 2 = 1) :
    ((Hcard : ℝ) - 1) ≤ ∑ x ∈ A, ‖χ x‖ ^ 2 := by
  have hsum : ∑ x ∈ A, ‖χ x‖ ^ 2 = ∑ x ∈ A, ‖α x‖ ^ 2 :=
    Finset.sum_congr rfl (fun x hx => by rw [hχ x hx])
  rw [hsum, hs]
  have hnat : Hcard - 1 ≤ s := caseB_eta_norm_core hP hn hParseval hInflation habelian
  have h := (Nat.cast_le (α := ℝ)).mpr hnat
  rwa [Nat.cast_sub hH, Nat.cast_one] at h

/-- **Arithmetic assembly of Peterfalvi (13.8)**: the norm lower bound
`∑_{x∈H#}|η₀₁(x)|² ≥ |S'| − u²`.

By (13.3.c) there are `j` and `δ = ±1` with `μ_j^{τ₁} = δ ∑_{0≤i<q} η_{i1}`, so the (13.5)
hypothesis
holds with `ζ₁ = μ_j` (degree `qu`, `‖μ_j‖² = q`), `χ = η₀₁`, `a = δ`. The (13.5.b) decomposition
then
gives `s = firstTerm − 2δu·α(1) + sₐ` where
`firstTerm = (1/q)(|S| − (qu)²/q) = |S|/q − u² = |S'| − u²`
(as `[S:S'] = q`) and `sₐ = ∑_{H#}|α|²`. With `(|P|−1)α(1)² ≤ sₐ` (13.5.c), `α(1) ∈ ℤ`, `δ² = 1`,
and
`2u ≤ |P|−1` (13.2.c), the cross terms are nonnegative — setting `b = δ·α(1)`,
`−2δu·α(1) + (|P|−1)α(1)² = (|P|−1)b² − 2ub ≥ 0` (`caseB_quadratic_nonneg`) — whence
`firstTerm ≤ s`.
Carrier-free arithmetic core; the character-theoretic decomposition is supplied by the (13.5)
engine. -/
theorem caseB_eta01_norm_core {Pm1 u : ℕ} {firstTerm s sₐ : ℝ} {α1 δ : ℤ}
    (hδ : δ ^ 2 = 1)
    (hdecomp : s = firstTerm - 2 * (δ : ℝ) * u * α1 + sₐ)
    (hinfl : (Pm1 : ℝ) * (α1 : ℝ) ^ 2 ≤ sₐ)
    (hu : 2 * u ≤ Pm1) :
    firstTerm ≤ s := by
  have hquad : (0 : ℤ) ≤ (Pm1 : ℤ) * (δ * α1) ^ 2 - 2 * (u : ℤ) * (δ * α1) :=
    caseB_quadratic_nonneg hu (δ * α1)
  have hquadR : (0 : ℝ) ≤ (Pm1 : ℝ) * ((δ : ℝ) * α1) ^ 2 - 2 * (u : ℝ) * ((δ : ℝ) * α1) := by
    exact_mod_cast hquad
  have hδR : (δ : ℝ) ^ 2 = 1 := by exact_mod_cast hδ
  have hcross : 0 ≤ -2 * (δ : ℝ) * u * α1 + sₐ := by
    have hsq : ((δ : ℝ) * α1) ^ 2 = (α1 : ℝ) ^ 2 := by rw [mul_pow, hδR, one_mul]
    have hfac : (Pm1 : ℝ) * ((δ : ℝ) * α1) ^ 2 - 2 * (u : ℝ) * ((δ : ℝ) * α1)
        = (Pm1 : ℝ) * (α1 : ℝ) ^ 2 - 2 * (δ : ℝ) * u * α1 := by rw [hsq]; ring
    nlinarith [hinfl, hfac, hquadR]
  linarith [hdecomp, hcross]

open scoped Classical in
/-- **Peterfalvi (13.8), character-theoretic bound**: the norm lower bound
`∑_{x∈H#}|η₀₁(x)|² ≥ firstTerm` (textbook `|S'| − u²`), assembled from the (13.5) machinery.

For `χ = η₀₁` the (13.5) hypothesis holds with `ζ = μ_j` (`‖μ_j‖² = 1`) and `a = δ = ±1`, so the
inflation factor is `κ = δ`.  This chains `sum_normSq_sharp_chi_decomp` (with `κ = δ`) into the
arithmetic core `caseB_eta01_norm_core`; `δ² = 1` collapses the `ζ`-term coefficient.  The
character-theoretic content is exposed as explicit honest hypotheses (discharged from the (13.8)
setup): `hvanish`/`hinner` as in (13.6); `hχ` the (13.5.a) point formula `η₀₁ = δ·μ_j + α` on `H#`;
`hfirstTerm` identifies `∑_S|μ_j|² − μ_j(1)²` with `firstTerm`; `hcross` the cross term
`Re(μ_j(1)·conj α(1)) = u·α(1)`; `hinfl` (13.5.c); `hu` (13.2.c). -/
theorem caseB_eta01_norm_bound {S : Type*} [Group S] [Fintype S]
    (H : Subgroup S) (ζ α χ : S → ℂ) {Pm1 u : ℕ} {firstTerm : ℝ} {α1 δ : ℤ}
    (hvanish : ∀ x : S, x ∉ H → ζ x = 0)
    (hinner : ∑ x ∈ Finset.univ.filter (· ∈ H), ζ x * (starRingEnd ℂ) (α x) = 0)
    (hχ : ∀ x ∈ (Finset.univ.filter (· ∈ H)).erase 1, χ x = (δ : ℂ) * ζ x + α x)
    (hfirstTerm : (∑ x : S, ‖ζ x‖ ^ 2) - ‖ζ 1‖ ^ 2 = firstTerm)
    (hcross : (ζ 1 * (starRingEnd ℂ) (α 1)).re = (u : ℝ) * (α1 : ℝ))
    (hδ : δ ^ 2 = 1)
    (hinfl : (Pm1 : ℝ) * (α1 : ℝ) ^ 2
        ≤ ∑ x ∈ (Finset.univ.filter (· ∈ H)).erase 1, ‖α x‖ ^ 2)
    (hu : 2 * u ≤ Pm1) :
    firstTerm ≤ ∑ x ∈ (Finset.univ.filter (· ∈ H)).erase 1, ‖χ x‖ ^ 2 := by
  refine caseB_eta01_norm_core hδ ?_ hinfl hu
  have hδR : (δ : ℝ) ^ 2 = 1 := by exact_mod_cast hδ
  rw [sum_normSq_sharp_chi_decomp H ζ α χ (δ : ℝ) hvanish hinner
    (by intro x hx; rw [hχ x hx]; push_cast; ring), hcross, hfirstTerm, hδR]
  ring

end OddOrder.Peterfalvi.S15

-- ===== OddOrder/Peterfalvi/S15_SAndT_Setup/DegreesFirstSplit.lean =====
namespace OddOrder.Peterfalvi.S15

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

open OddOrder.Isaacs

open scoped Pointwise

variable {G : Type*} [Group G]

/-- The defining property of `normSqSumQ` on its good domain. -/
theorem normSqSumQ_spec {H : Type*} [Group H] {A : Finset H} {χ : ClassFunction H ℂ}
    (h : ∃ n : ℕ, (n : ℝ) = ∑ x ∈ A, ‖χ x‖ ^ 2) :
    ((normSqSumQ A χ : ℚ) : ℝ) = ∑ x ∈ A, ‖χ x‖ ^ 2 := by
  rw [normSqSumQ, dif_pos h]
  exact_mod_cast Classical.choose_spec h

open scoped FiniteInduce in
/-- **`η₁₀` is a virtual character of `G`** — real content of the 3002-threaded grid:
`η₁₀ = τ₃(ω₁₀)` (`eta_eq_tau_omega`), `ω₁₀ ∈ ZIrr W` (`omega_mem_ZIrr`), and `τ₃` preserves
virtual characters (`tau3_mem_ZIrr`). -/
theorem Hypothesis.eta10_mem_ZIrr [Finite G] (hyp : Hypothesis (G := G)) :
    hyp.eta10 ∈ ZIrr G := by
  rw [Hypothesis.eta10, hyp.eta_eq_tau_omega]
  exact hyp.tau3_mem_ZIrr _ (hyp.omega_mem_ZIrr _ _)

end OddOrder.Peterfalvi.S15

-- ===== OddOrder/Peterfalvi/S15_SAndT_Setup/CountingLayer.lean =====
namespace OddOrder.Peterfalvi.S15

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

open OddOrder.Isaacs

open scoped Pointwise

variable {G : Type*} [Group G]

section CountingLayer

open OddOrder.GroupTheory

/-- `|T| = |Q|·(vd)·p` — the `T`-side order decomposition, read off the reconciled type-`P`
datum (`M_complement`/`derived_complement` of `reconciled_typePData_T`) with `|V| = vd` and
`|W₂| = p`. -/
theorem Hypothesis.card_T_eq [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) :
    Nat.card ↥hyp.T = Nat.card ↥hyp.Q * (hyp.v * hyp.d) * hyp.p := by
  obtain ⟨tpd, hU, hW1, -⟩ := reconciled_typePData_T hG hyp
  -- `|T| = |T'|·p`.
  have hle : derivedInG hyp.T ≤ hyp.T := Subgroup.map_subtype_le _
  have h1 := tpd.M_complement.card_mul_card
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe tpd.W1_le).toEquiv,
    hW1, ← hyp.p_eq_card_W2] at h1
  -- `|T'| = |Q|·|V| = |Q|·(vd)`.
  have h2 := tpd.derived_complement.card_mul_card
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe tpd.H_le).toEquiv,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe tpd.U_le).toEquiv, tpd.H_eq, ← hyp.Q_eq_TF,
    hU, hyp.card_V_eq_vd] at h2
  rw [← h1, ← h2]

open scoped FiniteInduce in
/-- **Global Parseval four-piece split** for a norm-`1` class function (the shared spine of the
Peterfalvi (13.10.1)/(13.10.2) estimates):

  `|G| = ‖φ(1)‖² + ∑_{G₀}‖φ‖² + [G:S]·∑_{H^#}‖φ‖² + [G:T]·∑_{Q^#}‖φ‖²`.

The total `∑_G ‖φ‖² = |G|·⟨φ,φ⟩ = |G|` (Parseval, `sum_normSq_eq_card_mul_inner`), split by the
four-piece decomposition `sum_univ_split` (the summand `‖φ(·)‖²` is conjugation-invariant since
`φ` is a class function). -/
theorem Hypothesis.global_normSq_split [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) (φ : ClassFunction G ℂ)
    (hn : ClassFunction.inner φ φ = 1)
    (hcardQ : Nat.card ↥hyp.Q = hyp.q ^ hyp.p) (hvd : hyp.v * hyp.d ≠ 1) :
    (Nat.card G : ℝ)
      = ‖φ 1‖ ^ 2 + (∑ x ∈ hyp.G0Finset, ‖φ x‖ ^ 2)
        + hyp.S.index • (∑ x ∈ (Set.toFinite (sharpSubgroup hyp.H)).toFinset, ‖φ x‖ ^ 2)
        + hyp.T.index • (∑ x ∈ (Set.toFinite (sharpSubgroup hyp.Q)).toFinset, ‖φ x‖ ^ 2) := by
  have hsplit := hyp.sum_univ_split hG (fun x => ‖φ x‖ ^ 2)
    (fun g x => by
      show ‖φ (g * x * g⁻¹)‖ ^ 2 = ‖φ x‖ ^ 2
      rw [ClassFunction.conj_eq φ x g]) hcardQ hvd
  have htotal : ((∑ x : G, ‖φ x‖ ^ 2 : ℝ) : ℂ) = (Nat.card G : ℂ) := by
    rw [sum_normSq_eq_card_mul_inner, hn, mul_one]
  have htotalR : ∑ x : G, ‖φ x‖ ^ 2 = (Nat.card G : ℝ) := by exact_mod_cast htotal
  rw [← htotalR, hsplit]

end CountingLayer

end OddOrder.Peterfalvi.S15

-- ===== OddOrder/Peterfalvi/S15_SAndT_Setup/Canonicalization.lean =====
namespace OddOrder.Peterfalvi.S15

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

open OddOrder.Isaacs

open scoped Pointwise

variable {G : Type*} [Group G]

/-- The (13.4) case-(b) parameters, unpacked: `d = 1`, `v ≥ 2`, and (for the type-V exclusion
of the counting layer) `vd ≠ 1`. -/
theorem Hypothesis.caseB_vd_facts (hyp : Hypothesis (G := G))
    (hD : hyp.D = ⊥) (hv : hyp.v = (hyp.q ^ hyp.p - 1) / (hyp.q - 1)) :
    hyp.d = 1 ∧ 2 ≤ hyp.v ∧ hyp.v * hyp.d ≠ 1 := by
  have hd1 : hyp.d = 1 := by rw [hyp.d_eq_card_D, hD, Subgroup.card_bot]
  have hq3 : 3 ≤ hyp.q := hyp.three_le_q
  have hqp_ge : hyp.q * hyp.q ≤ hyp.q ^ hyp.p := by
    calc hyp.q * hyp.q = hyp.q ^ 2 := (sq hyp.q).symm
      _ ≤ hyp.q ^ hyp.p := Nat.pow_le_pow_right (by omega)
        (by have := hyp.three_le_p; omega)
  have hv2 : 2 ≤ hyp.v := by
    rw [hv, Nat.le_div_iff_mul_le (by omega : 0 < hyp.q - 1)]
    have h3q : 3 * hyp.q ≤ hyp.q * hyp.q := Nat.mul_le_mul_right _ hq3
    omega
  exact ⟨hd1, hv2, by rw [hd1, mul_one]; omega⟩

open scoped FiniteInduce in
/-- **`‖η₁₀‖² = 1`** — real content of the 3002-threaded grid: `τ₃` is an isometry
(`tau3_isometry`) and the `ω`-grid is orthonormal (`omega_orthonormal`). -/
theorem Hypothesis.eta10_inner_self_one [Finite G] (hyp : Hypothesis (G := G)) :
    ClassFunction.inner hyp.eta10 hyp.eta10 = 1 := by
  rw [Hypothesis.eta10, hyp.eta_eq_tau_omega, hyp.tau3_isometry.inner_eq,
    hyp.omega_orthonormal]
  simp

open scoped Classical in
/-- **Sharp-set sum transport** (subgroup-of form ↔ ambient form): for `K ≤ L`, a sum over the
nonidentity `K`-members *inside `↥L`* equals the sum over the ambient sharp `K^# ⊂ G`.  The
bridge between the (13.5)/(13.6) engines (stated inside the abstract ambient `↥S` with
`H.subgroupOf S`) and the (13.10) counting layer (stated over `sharpSubgroup K ⊂ G`). -/
theorem sum_apply_erase_one_filter_subgroupOf [Finite G] {M : Type*} [AddCommMonoid M]
    {K L : Subgroup G} [Fintype ↥L] (hKL : K ≤ L) (f : G → M) :
    ∑ x ∈ (Finset.univ.filter (· ∈ K.subgroupOf L)).erase 1, f ↑x
      = ∑ x ∈ (Set.toFinite (sharpSubgroup K)).toFinset, f x := by
  classical
  refine Finset.sum_bij' (fun x _ => (↑x : G))
    (fun y hy => (⟨y, hKL ((Set.Finite.mem_toFinset _).mp hy).1⟩ : ↥L)) ?_ ?_ ?_ ?_ ?_
  · intro x hx
    obtain ⟨hx1, hxK⟩ := Finset.mem_erase.mp hx
    rw [Set.Finite.mem_toFinset]
    refine ⟨Subgroup.mem_subgroupOf.mp (Finset.mem_filter.mp hxK).2, ?_⟩
    intro h1
    rw [Set.mem_singleton_iff] at h1
    exact hx1 (Subtype.ext h1)
  · intro y hy
    obtain ⟨hyK, hy1⟩ := (Set.Finite.mem_toFinset _).mp hy
    refine Finset.mem_erase.mpr ⟨?_, Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, Subgroup.mem_subgroupOf.mpr hyK⟩⟩
    intro h1
    exact hy1 (by simpa using congrArg (Subtype.val) h1)
  · intro x hx
    rfl
  · intro y hy
    rfl
  · intro x hx
    rfl

end OddOrder.Peterfalvi.S15

-- ===== OddOrder/Peterfalvi/S15_SAndT_Setup/NormEstimates.lean =====
namespace OddOrder.Peterfalvi.S15

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

open OddOrder.Isaacs

open scoped Pointwise

variable {G : Type*} [Group G]

/-- **`2v ≤ |Q| − 1`** — the `T`-side mirror of `two_mul_u_le`: from the (13.4) value
`v = (q^p − 1)/(q − 1)` and `q ≥ 3`, so `v ≤ (q^p−1)/2`. -/
theorem Hypothesis.two_mul_v_le (hyp : Hypothesis (G := G))
    (hv : hyp.v = (hyp.q ^ hyp.p - 1) / (hyp.q - 1)) :
    2 * hyp.v ≤ hyp.q ^ hyp.p - 1 := by
  have hq3 := hyp.three_le_q
  have h1 : (hyp.q ^ hyp.p - 1) / (hyp.q - 1) ≤ (hyp.q ^ hyp.p - 1) / 2 :=
    Nat.div_le_div_left (by omega) (by omega)
  have h2 : (hyp.q ^ hyp.p - 1) / 2 * 2 ≤ hyp.q ^ hyp.p - 1 := Nat.div_mul_le_self _ _
  omega

end OddOrder.Peterfalvi.S15

-- ===== OddOrder/Peterfalvi/S15_CaseBEndgameSupply/Eta10HCorrection.lean =====
namespace OddOrder.Peterfalvi.S15

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

open OddOrder.Isaacs

variable {G : Type*} [Group G]

section

open scoped Classical in
/-- **Peterfalvi (13.7), honest Core form**:
`∑_{x∈H^#}|η₁₀(x)|² ≥ |H| - 1`.  The character-theoretic correction data are constructed
above and the remaining implication is the abstract integral norm engine
`caseB_eta_norm_bound`. -/
theorem CharacterDegreeCore.eta10_Hsharp_norm_lower_core [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {hyp : Hypothesis (G := G)}
    (core : CharacterDegreeCore hyp) :
    (Nat.card ↥hyp.H : ℝ) - 1
      ≤ ∑ x ∈ (Set.toFinite (sharpSubgroup hyp.H)).toFinset, ‖hyp.eta10 x‖ ^ 2 := by
  obtain ⟨α, d, n, s, hχ, hs, hn, hParseval, hInflation, habelian⟩ :=
    core.exists_caseB_data_eta10_H_core hG
  have hH1 : 1 ≤ Nat.card ↥hyp.H :=
    Nat.one_le_iff_ne_zero.mpr Nat.card_pos.ne'
  have hP2 : 2 ≤ hyp.p ^ hyp.q - 1 + 1 := by
    have h1 : 3 ≤ hyp.p ^ hyp.q := by
      calc 3 ≤ hyp.p := hyp.three_le_p
        _ ≤ hyp.p ^ hyp.q := Nat.le_self_pow hyp.q_prime.ne_zero _
    omega
  have : Fintype G := Fintype.ofFinite G
  exact caseB_eta_norm_bound (S := G) α (fun x => hyp.eta10 x)
    ((Set.toFinite (sharpSubgroup hyp.H)).toFinset)
    (Hcard := Nat.card ↥hyp.H) (P := hyp.p ^ hyp.q - 1 + 1)
    (d := d) (n := n) (s := s) hH1 (fun x hx => hχ x hx) hs hP2 hn
    hParseval (by simpa using hInflation) habelian

end

end OddOrder.Peterfalvi.S15

-- ===== OddOrder/Peterfalvi/S15_CaseBEndgameSupply/Eta10Correction.lean =====
namespace OddOrder.Peterfalvi.S15

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

open OddOrder.Isaacs

variable {G : Type*} [Group G]

section

open scoped Classical in
open scoped FiniteInduce in
/-- **Peterfalvi (13.8), honest `T`-side norm bound**:
`∑_{x∈Q^#}|η₁₀(x)|² ≥ |T'| - v²` from the coefficient-zero chosen-base correction.
The two Case-B structural values are explicit inputs, and commutativity is precisely the
abelian half of the `Q` elementary-abelian conclusion used by the chosen-family engine. -/
theorem Hypothesis.eta10_Qsharp_norm_lower_core [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (hD : hyp.D = ⊥)
    (hv : hyp.v = (hyp.q ^ hyp.p - 1) / (hyp.q - 1))
    (hQcomm : IsMulCommutative ↥hyp.Q) (pins : NuGridSupplyData hyp) :
    (Nat.card ↥(derivedInG hyp.T) : ℝ) - (hyp.v : ℝ) ^ 2
      ≤ ∑ x ∈ (Set.toFinite (sharpSubgroup hyp.Q)).toFinset, ‖hyp.eta10 x‖ ^ 2 := by
  classical
  obtain ⟨ζ, α, α1, δ, hvanish, hinner, hχ, hfirstTerm, hcross, hδ, hinfl⟩ :=
    hyp.exists_caseB_data_eta10_T_core hG hD hQcomm pins
  have hQT : hyp.Q ≤ hyp.T := by
    rw [hyp.Q_eq_TF]
    exact OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le hyp.T
  have hu := hyp.two_mul_v_le hv
  have hengine : (Nat.card ↥(derivedInG hyp.T) : ℝ) - (hyp.v : ℝ) ^ 2
      ≤ ∑ x ∈ (Finset.univ.filter (· ∈ hyp.Q.subgroupOf hyp.T)).erase 1,
          ‖hyp.eta10 ↑x‖ ^ 2 := by
    have h := caseB_eta01_norm_bound (S := ↥hyp.T) (hyp.Q.subgroupOf hyp.T)
      ζ α (fun x => hyp.eta10 ↑x)
      (Pm1 := hyp.q ^ hyp.p - 1) (u := hyp.v)
      (firstTerm := (Nat.card ↥(derivedInG hyp.T) : ℝ) - (hyp.v : ℝ) ^ 2)
      (α1 := α1) (δ := δ)
      hvanish (by convert hinner using 2)
      (fun x hx => hχ x (by convert hx using 2))
      hfirstTerm hcross hδ
      (by convert hinfl using 2; congr!) hu
    convert h using 2; congr!
  rwa [sum_apply_erase_one_filter_subgroupOf hQT
    (fun y => ‖hyp.eta10 y‖ ^ 2)] at hengine

end

end OddOrder.Peterfalvi.S15

-- ===== OddOrder/Peterfalvi/S15_CaseBEndgameSupply/AnalyticRelayer.lean =====
namespace OddOrder.Peterfalvi.S15

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

open OddOrder.Isaacs

variable {G : Type*} [Group G]

section

open scoped FiniteInduce in
/-- **Peterfalvi (13.7)+(13.8), Core form**: the second analytic estimate in (13.10).

The `H^#` and `Q^#` lower bounds are supplied by the two chosen-base correction
packages.  The latter uses exactly the explicit case-B facts and commutativity of `Q`;
the remaining cardinal identities are derived in place. -/
theorem _root_.solution [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {hyp : Hypothesis (G := G)}
    (core : CharacterDegreeCore hyp)
    (hD : hyp.D = ⊥) (hv : hyp.v = (hyp.q ^ hyp.p - 1) / (hyp.q - 1))
    (hQcomm : IsMulCommutative ↥hyp.Q) (pins : NuGridSupplyData hyp) :
    (1 : ℚ) ≥ 1 / (Nat.card G : ℚ)
        + normSqSumQ hyp.G0Finset hyp.eta10 / (Nat.card G : ℚ)
        + ((Nat.card hyp.H - 1 : ℕ) : ℚ) / (Nat.card hyp.S : ℚ)
        + (1 / (hyp.p : ℚ) - 1 / ((hyp.p : ℚ) * ((hyp.q : ℚ) - 1))
          + 1 / ((hyp.p : ℚ) * ((hyp.q : ℚ) - 1) * (hyp.q : ℚ) ^ hyp.p)) := by
  classical
  have hQ : Nat.card ↥hyp.Q = hyp.q ^ hyp.p := hyp.card_Q_eq_qp hG
  obtain ⟨hd1, hv2, hvd⟩ := hyp.caseB_vd_facts hD hv
  have hZ := hyp.eta10_mem_ZIrr
  have hn := hyp.eta10_inner_self_one
  have hsplit := hyp.global_normSq_split hG hyp.eta10 hn hQ hvd
  have hone : (1 : ℝ) ≤ ‖hyp.eta10 1‖ ^ 2 :=
    OddOrder.RepresentationTheory.one_le_normSq_apply_one_of_mem_ZIrr_of_inner_self_one hZ hn
  have hsharpH := core.eta10_Hsharp_norm_lower_core hG
  have hsharpQ := hyp.eta10_Qsharp_norm_lower_core hG hD hv hQcomm pins
  have hGal := OddOrder.Algebra.exists_nat_sum_normSq_of_mem_ZIrr_of_cyclicClosed hZ
    hyp.G0Finset_cyclicClosed
  have hspec := normSqSumQ_spec hGal
  have hg0 : (0 : ℝ) < (Nat.card G : ℝ) := by exact_mod_cast Nat.card_pos (α := G)
  have hq3 : 3 ≤ hyp.q := hyp.three_le_q
  have hp3 : 3 ≤ hyp.p := hyp.three_le_p
  have hqp1 : (1 : ℕ) ≤ hyp.q ^ hyp.p := Nat.one_le_pow _ _ (by omega)
  have hdvd : (hyp.q - 1) ∣ (hyp.q ^ hyp.p - 1) := by
    simpa only [one_pow] using Nat.sub_dvd_pow_sub_pow hyp.q 1 hyp.p
  have hvq : (hyp.v : ℝ) * ((hyp.q : ℝ) - 1) = (hyp.q : ℝ) ^ hyp.p - 1 := by
    have h := Nat.div_mul_cancel hdvd
    rw [← hv] at h
    have := congrArg (Nat.cast (R := ℝ)) h
    push_cast [Nat.cast_sub (by omega : (1 : ℕ) ≤ hyp.q), Nat.cast_sub hqp1] at this
    convert this using 2
  have hderivT : (Nat.card ↥(derivedInG hyp.T) : ℝ) =
      (hyp.q : ℝ) ^ hyp.p * (hyp.v : ℝ) := by
    have h := hyp.card_deriv_T_eq hG
    rw [hQ, hd1, mul_one] at h
    exact_mod_cast h
  have hTval : (Nat.card ↥hyp.T : ℝ) =
      (hyp.q : ℝ) ^ hyp.p * (hyp.v : ℝ) * (hyp.p : ℝ) := by
    have h := hyp.card_T_eq hG
    rw [hQ, hd1, mul_one] at h
    exact_mod_cast h
  have hSGeq : (hyp.S.index : ℝ) * (Nat.card ↥hyp.S : ℝ) = (Nat.card G : ℝ) := by
    exact_mod_cast mul_comm (Nat.card ↥hyp.S) hyp.S.index ▸ hyp.S.card_mul_index
  have hTGeq : (hyp.T.index : ℝ) * (Nat.card ↥hyp.T : ℝ) = (Nat.card G : ℝ) := by
    exact_mod_cast mul_comm (Nat.card ↥hyp.T) hyp.T.index ▸ hyp.T.card_mul_index
  have hS0 : (0 : ℝ) < (Nat.card ↥hyp.S : ℝ) := by
    exact_mod_cast Nat.card_pos (α := ↥hyp.S)
  have hT0 : (0 : ℝ) < (Nat.card ↥hyp.T : ℝ) := by
    exact_mod_cast Nat.card_pos (α := ↥hyp.T)
  have hSidx0 : (0 : ℝ) < (hyp.S.index : ℝ) := by
    rcases (Nat.cast_pos (α := ℝ)).mpr (Nat.pos_of_ne_zero
      (Subgroup.index_ne_zero_of_finite (H := hyp.S))) with h
    exact h
  have hTidx0 : (0 : ℝ) < (hyp.T.index : ℝ) := by
    rcases (Nat.cast_pos (α := ℝ)).mpr (Nat.pos_of_ne_zero
      (Subgroup.index_ne_zero_of_finite (H := hyp.T))) with h
    exact h
  have hp0 : (0 : ℝ) < (hyp.p : ℝ) := by exact_mod_cast (by omega : 0 < hyp.p)
  have hq10 : (0 : ℝ) < (hyp.q : ℝ) - 1 := by
    have : (3 : ℝ) ≤ (hyp.q : ℝ) := by exact_mod_cast hq3
    linarith
  have hqp0 : (0 : ℝ) < (hyp.q : ℝ) ^ hyp.p := by
    have : (0 : ℝ) < (hyp.q : ℝ) := by exact_mod_cast (by omega : 0 < hyp.q)
    positivity
  have hv0 : (0 : ℝ) < (hyp.v : ℝ) := by exact_mod_cast (by omega : 0 < hyp.v)
  rw [ge_iff_le, ← Rat.cast_le (K := ℝ)]
  push_cast
  rw [hspec]
  set s : ℝ := ∑ x ∈ hyp.G0Finset, ‖hyp.eta10 x‖ ^ 2 with hsdef
  set sH : ℝ := ∑ x ∈ (Set.toFinite (sharpSubgroup hyp.H)).toFinset,
    ‖hyp.eta10 x‖ ^ 2 with hsHdef
  set sQ : ℝ := ∑ x ∈ (Set.toFinite (sharpSubgroup hyp.Q)).toFinset,
    ‖hyp.eta10 x‖ ^ 2 with hsQdef
  rw [nsmul_eq_mul, nsmul_eq_mul] at hsplit
  set TT : ℝ := 1 / (hyp.p : ℝ) - 1 / ((hyp.p : ℝ) * ((hyp.q : ℝ) - 1))
      + 1 / ((hyp.p : ℝ) * ((hyp.q : ℝ) - 1) * (hyp.q : ℝ) ^ hyp.p) with hTTdef
  have hveq : (hyp.v : ℝ) = ((hyp.q : ℝ) ^ hyp.p - 1) / ((hyp.q : ℝ) - 1) := by
    rw [eq_div_iff hq10.ne']
    exact hvq
  have hTT : TT = ((Nat.card ↥(derivedInG hyp.T) : ℝ) - (hyp.v : ℝ) ^ 2) /
      (Nat.card ↥hyp.T : ℝ) := by
    rw [hTTdef, hderivT, hTval, hveq]
    have hqp1' : (1 : ℝ) < (hyp.q : ℝ) ^ hyp.p := by
      have h1 : (1 : ℕ) < hyp.q ^ hyp.p := by
        calc 1 < hyp.q := by omega
          _ ≤ hyp.q ^ hyp.p := Nat.le_self_pow (by omega) _
      exact_mod_cast h1
    have hnum0 : (hyp.q : ℝ) ^ hyp.p - 1 ≠ 0 := by linarith
    field_simp
    ring
  have hH1 : (1 : ℕ) ≤ Nat.card ↥hyp.H := Nat.one_le_iff_ne_zero.mpr Nat.card_pos.ne'
  have hterm3 : ((Nat.card ↥hyp.H - 1 : ℕ) : ℝ) / (Nat.card ↥hyp.S : ℝ)
      = (hyp.S.index : ℝ) * ((Nat.card ↥hyp.H : ℝ) - 1) / (Nat.card G : ℝ) := by
    rw [← hSGeq, Nat.cast_sub hH1, Nat.cast_one,
      mul_div_mul_left _ _ hSidx0.ne']
  have hterm4 : TT = (hyp.T.index : ℝ)
      * ((Nat.card ↥(derivedInG hyp.T) : ℝ) - (hyp.v : ℝ) ^ 2) /
        (Nat.card G : ℝ) := by
    rw [hTT, ← hTGeq, mul_div_mul_left _ _ hTidx0.ne']
  have hbound : 1 + s + (hyp.S.index : ℝ) * ((Nat.card ↥hyp.H : ℝ) - 1)
      + (hyp.T.index : ℝ) *
        ((Nat.card ↥(derivedInG hyp.T) : ℝ) - (hyp.v : ℝ) ^ 2)
      ≤ (Nat.card G : ℝ) := by
    have hHb := mul_le_mul_of_nonneg_left hsharpH hSidx0.le
    have hQb := mul_le_mul_of_nonneg_left hsharpQ hTidx0.le
    nlinarith [hsplit, hone, hHb, hQb]
  rw [hterm3, hterm4]
  have hfinal : (1 + s + (hyp.S.index : ℝ) * ((Nat.card ↥hyp.H : ℝ) - 1)
      + (hyp.T.index : ℝ) *
        ((Nat.card ↥(derivedInG hyp.T) : ℝ) - (hyp.v : ℝ) ^ 2)) /
      (Nat.card G : ℝ) ≤ 1 := by
    rw [div_le_one hg0]
    exact hbound
  calc 1 / (Nat.card G : ℝ) + s / (Nat.card G : ℝ)
        + (hyp.S.index : ℝ) * ((Nat.card ↥hyp.H : ℝ) - 1) / (Nat.card G : ℝ)
        + (hyp.T.index : ℝ) *
            ((Nat.card ↥(derivedInG hyp.T) : ℝ) - (hyp.v : ℝ) ^ 2) /
              (Nat.card G : ℝ)
      = (1 + s + (hyp.S.index : ℝ) * ((Nat.card ↥hyp.H : ℝ) - 1)
          + (hyp.T.index : ℝ) *
            ((Nat.card ↥(derivedInG hyp.T) : ℝ) - (hyp.v : ℝ) ^ 2)) /
          (Nat.card G : ℝ) := by
        rw [add_div, add_div, add_div]
    _ ≤ 1 := hfinal

end

end OddOrder.Peterfalvi.S15
