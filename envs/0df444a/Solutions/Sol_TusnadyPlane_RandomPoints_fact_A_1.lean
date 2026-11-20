-- Prove2me | solution 1 for TusnadyPlane.RandomPoints.fact_A_1
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T16:30:18.994166+00:00
-- url     : https://prove2.me/submissions/68dc6c67-b43c-49c6-a15d-152f3ccdce4a

import Mathlib.Probability.Moments.SubGaussian
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Tactic

section
/-!
# Fact A.1 of the manuscript (bounded differences), as stated

Auditor's supplement (not part of the audited archive).

**Fact A.1.** Let `ξ_1, …, ξ_n` be independent random variables, and let `Γ` be a random
element independent of `(ξ_1, …, ξ_n)`. Let `f = φ(Γ, ξ_1, …, ξ_n)` be integrable, where `φ`
is measurable and, for every value `γ` of `Γ`, changing the value of one `ξ_i` changes
`φ(γ, ·)` by at most `c > 0`. Then, for every real `t`, almost surely

`E[exp(t (f - E[f | Γ])) | Γ] ≤ exp(n t² c² / 2)`.

The proof is the one of Appendix A.2: conditioning on `Γ = γ` amounts to fixing the first
argument of `φ` (independence and Fubini); then the variables `ξ_1, …, ξ_n` are revealed one
at a time, and each step costs a factor `cosh(tc) ≤ exp(t²c²/2)`.

`bounded_differences_pi` is the unconditional bound for a product measure, and `fact_A_1` is
the fact as stated; `fact_A_1_integrable` says that the exponential in the statement is
integrable, so that its conditional expectation is the genuine one.

How the proof of the manuscript is carried out here:

* "Since `Γ` is independent of the `ξ_i`, conditioning on `Γ = γ` amounts to fixing the first
  argument of `φ`, by Fubini's theorem": `condExp_comap_eq_integral_of_indepFun` and
  `fact_A_1_freeze`.
* "Any two values of `f` differ by at most `nc`, so `f` is bounded":
  `abs_sub_le_of_bounded_differences`.
* "Martingale differences" and "All differences": for a product measure the conditional
  expectation of `f` given `ξ_1, …, ξ_i` is the integral of `f` over the later coordinates.
  `bounded_differences_pi` integrates the coordinates out one at a time, starting with the
  last one (`integral_pi_snoc`, Fubini), which is the successive conditioning on
  `ξ_1, …, ξ_{n-1}`, then on `ξ_1, …, ξ_{n-2}`, and so on. The martingale differences `Y_i`
  are not introduced as random variables: the function `g'` in the proof is `f_{n-1}`, and
  `g - g'` is `Y_n`.
* "One difference": the manuscript states this step for conditional expectations, "Let `𝓗` be
  a σ-field, and let `E[Y | 𝓗] = 0` and `|Y| ≤ c`", with the conclusion
  `E[e^{tY} | 𝓗] ≤ cosh(tc) ≤ e^{t²c²/2}` for every real `t`.
  - On the route of `fact_A_1`: `exp_mul_le_chord` is the convexity of `y ↦ exp(ty)` on
    `[-c, c]`; `cosh_le_exp_sq_half` is `cosh x ≤ exp(x²/2)`, by comparing the two Taylor
    series term by term with `(2k)! ≥ 2^k k!`; `integral_exp_le_cosh` is the bound
    `E exp(tY) ≤ cosh(tc)` for `E Y = 0`, `|Y| ≤ c`, without conditioning;
    `integral_exp_le_of_centered` continues it to `E exp(tY) ≤ exp(t²c²/2)`; and
    `integral_exp_centered_le` applies it to `Y = f - E f`. The bound is used for the last
    coordinate with the earlier ones fixed, that is, conditionally on `ξ_1, …, ξ_{n-1}`.
  - Restatements, not on the route of `fact_A_1`: `condExp_exp_le_cosh`
    (`E[exp(tY) | 𝓗] ≤ cosh(tc)`) and `condExp_exp_le_exp_sq`
    (`E[exp(tY) | 𝓗] ≤ exp(t²c²/2)`) are the step as the manuscript states it, for a
    sub-σ-field `𝓗` of the σ-field of a probability space. These two theorems are stand-alone
    statements of the manuscript's lemma: the proof of `fact_A_1` in this file works with
    product measures and does not need them.

The random variables `ξ_i` take values in an arbitrary measurable space `E` (the manuscript's
random variables are the case `E = ℝ`; Lemma 2.6 uses `E = {0, …, b-1}`), and `Γ` in an
arbitrary measurable space `G`. This file uses Mathlib only, not the archive.
-/

namespace R56Audit

open MeasureTheory ProbabilityTheory

noncomputable section

/-! ### Functions of bounded oscillation -/

/-- A real function whose values differ pairwise by at most `d` is bounded. -/
lemma exists_abs_le_of_abs_sub_le {α : Type*} {f : α → ℝ} {d : ℝ}
    (hosc : ∀ x y, |f x - f y| ≤ d) : ∃ C, ∀ x, |f x| ≤ C := by
  rcases isEmpty_or_nonempty α with h | ⟨⟨x₀⟩⟩
  · exact ⟨0, fun x => (h.false x).elim⟩
  · refine ⟨|f x₀| + d, fun x => ?_⟩
    have h1 := hosc x x₀
    have h2 := abs_sub_abs_le_abs_sub (f x) (f x₀)
    linarith

/-- A measurable function of bounded oscillation is integrable for a finite measure. -/
lemma integrable_of_abs_sub_le {α : Type*} [MeasurableSpace α] {μ : Measure α}
    [IsFiniteMeasure μ] {f : α → ℝ} (hf : Measurable f) {d : ℝ}
    (hosc : ∀ x y, |f x - f y| ≤ d) : Integrable f μ := by
  obtain ⟨C, hC⟩ := exists_abs_le_of_abs_sub_le hosc
  exact Integrable.of_bound hf.aestronglyMeasurable C (Filter.Eventually.of_forall hC)

/-- For `f` measurable of bounded oscillation, `exp (t (f - m))` is integrable (finite measure). -/
lemma integrable_exp_of_abs_sub_le {α : Type*} [MeasurableSpace α] {μ : Measure α}
    [IsFiniteMeasure μ] {f : α → ℝ} (hf : Measurable f) {d : ℝ}
    (hosc : ∀ x y, |f x - f y| ≤ d) (t m : ℝ) :
    Integrable (fun x => Real.exp (t * (f x - m))) μ := by
  obtain ⟨C, hC⟩ := exists_abs_le_of_abs_sub_le hosc
  exact integrable_exp_mul_of_mem_Icc (a := -C - m) (b := C - m) (hf.sub_const m).aemeasurable
    (Filter.Eventually.of_forall fun x =>
      ⟨by linarith [(abs_le.mp (hC x)).1], by linarith [(abs_le.mp (hC x)).2]⟩)

/-- On a probability space, functions that are pointwise `d`-close have `d`-close means. -/
lemma abs_integral_sub_integral_le {α : Type*} [MeasurableSpace α] {μ : Measure α}
    [IsProbabilityMeasure μ] {u v : α → ℝ} (hu : Integrable u μ) (hv : Integrable v μ) {d : ℝ}
    (h : ∀ a, |u a - v a| ≤ d) : |∫ a, u a ∂μ - ∫ a, v a ∂μ| ≤ d := by
  rw [← integral_sub hu hv]
  have := norm_integral_le_of_norm_le_const (μ := μ) (f := fun a => u a - v a)
    (Filter.Eventually.of_forall h)
  simpa using this

/-- On a probability space, a function of oscillation at most `d` is within `d` of its mean. -/
lemma abs_sub_integral_le {α : Type*} [MeasurableSpace α] {μ : Measure α}
    [IsProbabilityMeasure μ] {f : α → ℝ} (hf : Integrable f μ) {d : ℝ}
    (hosc : ∀ x y, |f x - f y| ≤ d) (x : α) : |f x - ∫ y, f y ∂μ| ≤ d := by
  have := abs_integral_sub_integral_le (integrable_const (f x)) hf (hosc x)
  simpa using this

/-! ### One difference -/

/-- `cosh x ≤ exp (x² / 2)`: the Taylor series `cosh x = Σ_k x^{2k} / (2k)!` and
`exp (x² / 2) = Σ_k x^{2k} / (2^k k!)` are compared term by term, using `(2k)! ≥ 2^k k!`. -/
lemma cosh_le_exp_sq_half (x : ℝ) : Real.cosh x ≤ Real.exp (x ^ 2 / 2) := by
  have hexp : ∀ z : ℝ, HasSum (fun n : ℕ => z ^ n / (n.factorial : ℝ)) (Real.exp z) := fun z => by
    rw [Real.exp_eq_exp_ℝ]
    exact NormedSpace.expSeries_div_hasSum_exp z
  -- the series of `cosh x = (exp x + exp (-x)) / 2`; its odd terms vanish
  have h3 : HasSum (fun n : ℕ => (x ^ n / (n.factorial : ℝ) + (-x) ^ n / (n.factorial : ℝ)) / 2)
      (Real.cosh x) := by
    rw [Real.cosh_eq]
    exact ((hexp x).add (hexp (-x))).div_const 2
  have hinj : Function.Injective (fun k : ℕ => 2 * k) := fun a b h => by
    simpa using h
  have h4 : HasSum (fun k : ℕ => x ^ (2 * k) / ((2 * k).factorial : ℝ)) (Real.cosh x) := by
    have h := (hinj.hasSum_iff
      (f := fun n : ℕ => (x ^ n / (n.factorial : ℝ) + (-x) ^ n / (n.factorial : ℝ)) / 2)
      (a := Real.cosh x) ?_).mpr h3
    · refine h.congr_fun fun k => ?_
      simp only [Function.comp_apply]
      rw [Even.neg_pow (even_two_mul k)]
      ring
    · intro n hn
      have hodd : Odd n := by
        rcases Nat.even_or_odd n with he | ho
        · obtain ⟨m, rfl⟩ := he
          exact absurd ⟨m, by ring⟩ hn
        · exact ho
      rw [Odd.neg_pow hodd]
      ring
  refine hasSum_le (fun k => ?_) h4 (hexp (x ^ 2 / 2))
  -- `x^{2k} / (2k)! ≤ (x²/2)^k / k!`
  rw [div_pow, pow_mul, div_div]
  apply div_le_div_of_nonneg_left (by positivity) (by positivity)
  exact_mod_cast Nat.two_pow_mul_factorial_le_factorial_two_mul k

/-- Convexity of `y ↦ exp (t y)` on `[-c, c]`: the graph lies below the chord. -/
lemma exp_mul_le_chord {c : ℝ} (hc : 0 < c) (t : ℝ) {y : ℝ} (hy : |y| ≤ c) :
    Real.exp (t * y) ≤
      (c + y) / (2 * c) * Real.exp (t * c) + (c - y) / (2 * c) * Real.exp (-(t * c)) := by
  have hy' := abs_le.mp hy
  have ha : 0 ≤ (c + y) / (2 * c) := div_nonneg (by linarith) (by positivity)
  have hb : 0 ≤ (c - y) / (2 * c) := div_nonneg (by linarith) (by positivity)
  have hab : (c + y) / (2 * c) + (c - y) / (2 * c) = 1 := by
    field_simp
    ring
  have h := convexOn_exp.2 (Set.mem_univ (t * c)) (Set.mem_univ (-(t * c))) ha hb hab
  simp only [smul_eq_mul] at h
  have he : (c + y) / (2 * c) * (t * c) + (c - y) / (2 * c) * -(t * c) = t * y := by
    field_simp
    ring
  rwa [he] at h

/-- **One difference** (Appendix A.2), without conditioning, the first inequality: if `E Y = 0`
and `|Y| ≤ c`, then `E exp (t Y) ≤ cosh (t c)`. The proof integrates the chord bound
`exp_mul_le_chord`: the chord is affine in `Y`, and `E Y = 0`, so its integral is `cosh (t c)`.

This lemma is on the route of `fact_A_1`; `condExp_exp_le_cosh` is the same bound for
conditional expectations, as the manuscript states it. -/
lemma integral_exp_le_cosh {α : Type*} [MeasurableSpace α] {μ : Measure α}
    [IsProbabilityMeasure μ] {Y : α → ℝ} (hY : Measurable Y) {c : ℝ} (hc : 0 < c)
    (hbd : ∀ x, |Y x| ≤ c) (hmean : ∫ x, Y x ∂μ = 0) (t : ℝ) :
    ∫ x, Real.exp (t * Y x) ∂μ ≤ Real.cosh (t * c) := by
  have hYi : Integrable Y μ :=
    Integrable.of_bound hY.aestronglyMeasurable c (Filter.Eventually.of_forall hbd)
  have hi1 : Integrable (fun x => (c + Y x) / (2 * c) * Real.exp (t * c)) μ :=
    (((integrable_const c).add hYi).div_const _).mul_const _
  have hi2 : Integrable (fun x => (c - Y x) / (2 * c) * Real.exp (-(t * c))) μ :=
    (((integrable_const c).sub hYi).div_const _).mul_const _
  -- integrate the chord bound; the integral of the chord is `cosh (t c)`, because `E Y = 0`
  calc ∫ x, Real.exp (t * Y x) ∂μ
      ≤ ∫ x, ((c + Y x) / (2 * c) * Real.exp (t * c) +
          (c - Y x) / (2 * c) * Real.exp (-(t * c))) ∂μ :=
        integral_mono_of_nonneg (Filter.Eventually.of_forall fun x => (Real.exp_pos _).le)
          (hi1.add hi2) (Filter.Eventually.of_forall fun x => exp_mul_le_chord hc t (hbd x))
    _ = Real.cosh (t * c) := by
        rw [integral_add hi1 hi2, integral_mul_const, integral_mul_const, integral_div,
          integral_div, integral_add (integrable_const c) hYi,
          integral_sub (integrable_const c) hYi, hmean, Real.cosh_eq]
        simp only [integral_const, probReal_univ, one_smul, add_zero, sub_zero]
        field_simp

/-- **One difference** (Appendix A.2), without conditioning: if `E Y = 0` and `|Y| ≤ c`, then
`E exp (t Y) ≤ cosh (t c) ≤ exp (t² c² / 2)`. The two inequalities are `integral_exp_le_cosh`
and `cosh_le_exp_sq_half`. -/
lemma integral_exp_le_of_centered {α : Type*} [MeasurableSpace α] {μ : Measure α}
    [IsProbabilityMeasure μ] {Y : α → ℝ} (hY : Measurable Y) {c : ℝ} (hc : 0 < c)
    (hbd : ∀ x, |Y x| ≤ c) (hmean : ∫ x, Y x ∂μ = 0) (t : ℝ) :
    ∫ x, Real.exp (t * Y x) ∂μ ≤ Real.exp (t ^ 2 * c ^ 2 / 2) :=
  calc ∫ x, Real.exp (t * Y x) ∂μ ≤ Real.cosh (t * c) := integral_exp_le_cosh hY hc hbd hmean t
    _ ≤ Real.exp ((t * c) ^ 2 / 2) := cosh_le_exp_sq_half _
    _ = Real.exp (t ^ 2 * c ^ 2 / 2) := by rw [mul_pow]

/-- One difference, for a function of oscillation at most `c`:
`E exp(t (f - E f)) ≤ exp(t²c²/2)`. -/
lemma integral_exp_centered_le {α : Type*} [MeasurableSpace α] {μ : Measure α}
    [IsProbabilityMeasure μ] {f : α → ℝ} (hf : Measurable f) {c : ℝ} (hc : 0 ≤ c)
    (hosc : ∀ x y, |f x - f y| ≤ c) (t : ℝ) :
    ∫ x, Real.exp (t * (f x - ∫ y, f y ∂μ)) ∂μ ≤ Real.exp (t ^ 2 * c ^ 2 / 2) := by
  have hfi : Integrable f μ := integrable_of_abs_sub_le hf hosc
  have hz : ∫ x, (f x - ∫ y, f y ∂μ) ∂μ = 0 := by
    rw [integral_sub hfi (integrable_const _)]
    simp
  rcases hc.eq_or_lt with rfl | hc'
  · -- `c = 0`: the function is constant
    have h0 : ∀ x, f x - ∫ y, f y ∂μ = 0 := fun x =>
      abs_eq_zero.mp (le_antisymm (abs_sub_integral_le hfi hosc x) (abs_nonneg _))
    simp [h0]
  · -- `Y = f - E f` has mean zero and `|Y| ≤ c`
    exact integral_exp_le_of_centered (hf.sub_const _) hc' (abs_sub_integral_le hfi hosc) hz t

/-! ### One difference, as the manuscript states it

The manuscript states the step for a σ-field `𝓗`: "Let `𝓗` be a σ-field, and let
`E[Y | 𝓗] = 0` and `|Y| ≤ c`." The next two theorems have this form. They are stand-alone
statements of the manuscript's lemma: the proof of `fact_A_1` in this file works with product
measures and does not need them. -/

/-! ### Bounded differences for a product of probability measures -/

/-- A function of `n` coordinates with differences bounded by `c` has oscillation at most `n c`. -/
lemma abs_sub_le_of_bounded_differences {E : Type*} {n : ℕ} (g : (Fin n → E) → ℝ) {c : ℝ}
    (hdiff : ∀ x i a, |g (Function.update x i a) - g x| ≤ c) (x y : Fin n → E) :
    |g x - g y| ≤ n * c := by
  induction n with
  | zero => simp [Subsingleton.elim x y]
  | succ n ih =>
    -- change the first `n` coordinates of `x` into those of `y`, then the last one
    have h1 : |g (Fin.snoc (Fin.init x) (x (Fin.last n))) -
        g (Fin.snoc (Fin.init y) (x (Fin.last n)))| ≤ n * c := by
      refine ih (fun p => g (Fin.snoc p (x (Fin.last n)))) (fun p i a => ?_) _ _
      rw [Fin.snoc_update]
      exact hdiff _ _ _
    have h2 : |g (Fin.snoc (Fin.init y) (y (Fin.last n))) -
        g (Fin.snoc (Fin.init y) (x (Fin.last n)))| ≤ c := by
      have := hdiff (Fin.snoc (Fin.init y) (x (Fin.last n))) (Fin.last n) (y (Fin.last n))
      rwa [Fin.update_snoc_last] at this
    rw [Fin.snoc_init_self] at h1 h2
    have h3 := abs_sub_le (g x) (g (Fin.snoc (Fin.init y) (x (Fin.last n)))) (g y)
    rw [abs_sub_comm (g (Fin.snoc (Fin.init y) (x (Fin.last n)))) (g y)] at h3
    push_cast
    linarith

/-- `Fin.snoc` is jointly measurable. -/
lemma measurable_snoc {E : Type*} [MeasurableSpace E] {n : ℕ} :
    Measurable fun p : (Fin n → E) × E => (Fin.snoc p.1 p.2 : Fin (n + 1) → E) := by
  refine measurable_pi_iff.2 fun j => ?_
  cases j using Fin.lastCases with
  | last =>
    simp only [Fin.snoc_last]
    exact measurable_snd
  | cast i =>
    simp only [Fin.snoc_castSucc]
    exact (measurable_pi_apply i).comp measurable_fst

/-- Fubini for the last coordinate of a finite product of probability measures. -/
lemma integral_pi_snoc {E : Type*} [MeasurableSpace E] {n : ℕ}
    (ν : Fin (n + 1) → Measure E) [∀ i, IsProbabilityMeasure (ν i)]
    {F : (Fin (n + 1) → E) → ℝ} (hF : Integrable F (Measure.pi ν)) :
    ∫ x, F x ∂Measure.pi ν =
      ∫ y, ∫ a, F (Fin.snoc y a) ∂ν (Fin.last n) ∂Measure.pi (fun i : Fin n => ν i.castSucc) := by
  have he : ∀ (a : E) (y : Fin n → E),
      (MeasurableEquiv.piFinSuccAbove (fun _ => E) (Fin.last n)).symm (a, y) = Fin.snoc y a :=
    fun a y => Fin.insertNth_last' a y
  have hmp := (measurePreserving_piFinSuccAbove ν (Fin.last n)).symm
  simp only [Fin.succAbove_last] at hmp
  rw [← hmp.integral_comp' F, integral_prod_symm]
  · simp only [he]
  · exact (hmp.integrable_comp_emb (MeasurableEquiv.measurableEmbedding _)).mpr hF

/-- **Bounded differences for a product of probability measures** (the unconditional bound in
the proof of Fact A.1): if changing one coordinate changes `g` by at most `c`, then
`E exp(t (g - E g)) ≤ exp(n t² c² / 2)`. -/
theorem bounded_differences_pi {E : Type*} [MeasurableSpace E] {n : ℕ}
    (ν : Fin n → Measure E) [∀ i, IsProbabilityMeasure (ν i)]
    (g : (Fin n → E) → ℝ) (hg : Measurable g) {c : ℝ} (hc : 0 ≤ c)
    (hdiff : ∀ x i a, |g (Function.update x i a) - g x| ≤ c) (t : ℝ) :
    ∫ x, Real.exp (t * (g x - ∫ y, g y ∂Measure.pi ν)) ∂Measure.pi ν ≤
      Real.exp (n * t ^ 2 * c ^ 2 / 2) := by
  induction n with
  | zero =>
    -- there is only one point, so `g - E g = 0`
    have hm : ∀ x, g x - ∫ y, g y ∂Measure.pi ν = 0 := fun x => by
      rw [integral_eq_const (Filter.Eventually.of_forall fun y =>
        congrArg g (Subsingleton.elim y x)), sub_self]
    simp [hm]
  | succ n ih =>
    -- `g` as a function of the last coordinate `a`, the first `n` coordinates being `y`
    have hgm : ∀ y : Fin n → E, Measurable fun a => g (Fin.snoc y a) := fun y =>
      hg.comp (measurable_snoc.comp measurable_prodMk_left)
    have hgosc : ∀ (y : Fin n → E) (a b : E), |g (Fin.snoc y a) - g (Fin.snoc y b)| ≤ c := by
      intro y a b
      have := hdiff (Fin.snoc y b) (Fin.last n) a
      rwa [Fin.update_snoc_last] at this
    have hgi : ∀ y : Fin n → E, Integrable (fun a => g (Fin.snoc y a)) (ν (Fin.last n)) :=
      fun y => integrable_of_abs_sub_le (hgm y) (hgosc y)
    -- `g'` is the average of `g` over the last coordinate; it has bounded differences
    let g' : (Fin n → E) → ℝ := fun y => ∫ a, g (Fin.snoc y a) ∂ν (Fin.last n)
    have hg' : Measurable g' :=
      ((hg.comp measurable_snoc).stronglyMeasurable.integral_prod_right').measurable
    have hg'diff : ∀ y i b, |g' (Function.update y i b) - g' y| ≤ c := by
      intro y i b
      refine abs_integral_sub_integral_le (hgi _) (hgi _) fun a => ?_
      rw [Fin.snoc_update]
      exact hdiff _ _ _
    -- `g'` and `g` have the same mean `m`
    have hm : ∫ y, g' y ∂Measure.pi (fun i : Fin n => ν i.castSucc) = ∫ x, g x ∂Measure.pi ν :=
      (integral_pi_snoc ν (integrable_of_abs_sub_le hg
        (abs_sub_le_of_bounded_differences g hdiff))).symm
    -- one difference: the last coordinate, the first `n` coordinates being fixed
    have hlast : ∀ y, ∫ a, Real.exp (t * (g (Fin.snoc y a) - g' y)) ∂ν (Fin.last n) ≤
        Real.exp (t ^ 2 * c ^ 2 / 2) := fun y =>
      integral_exp_centered_le (hgm y) hc (hgosc y) t
    -- all differences: split off the last one, and use the induction hypothesis for `g'`
    set m := ∫ x, g x ∂Measure.pi ν
    calc ∫ x, Real.exp (t * (g x - m)) ∂Measure.pi ν
        = ∫ y, ∫ a, Real.exp (t * (g (Fin.snoc y a) - m)) ∂ν (Fin.last n)
            ∂Measure.pi (fun i : Fin n => ν i.castSucc) :=
          integral_pi_snoc ν (integrable_exp_of_abs_sub_le hg
            (abs_sub_le_of_bounded_differences g hdiff) t m)
      _ = ∫ y, Real.exp (t * (g' y - m)) *
            ∫ a, Real.exp (t * (g (Fin.snoc y a) - g' y)) ∂ν (Fin.last n)
            ∂Measure.pi (fun i : Fin n => ν i.castSucc) := by
          congr 1 with y
          rw [← integral_const_mul]
          congr 1 with a
          rw [← Real.exp_add]
          congr 1
          ring
      _ ≤ ∫ y, Real.exp (t * (g' y - m)) * Real.exp (t ^ 2 * c ^ 2 / 2)
            ∂Measure.pi (fun i : Fin n => ν i.castSucc) := by
          refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun y => ?_)
            ((integrable_exp_of_abs_sub_le hg'
              (abs_sub_le_of_bounded_differences g' hg'diff) t m).mul_const _)
            (Filter.Eventually.of_forall fun y =>
              mul_le_mul_of_nonneg_left (hlast y) (Real.exp_pos _).le)
          exact mul_nonneg (Real.exp_pos _).le (integral_nonneg fun a => (Real.exp_pos _).le)
      _ = (∫ y, Real.exp (t * (g' y - m)) ∂Measure.pi (fun i : Fin n => ν i.castSucc)) *
            Real.exp (t ^ 2 * c ^ 2 / 2) := integral_mul_const _ _
      _ ≤ Real.exp (n * t ^ 2 * c ^ 2 / 2) * Real.exp (t ^ 2 * c ^ 2 / 2) := by
          rw [← hm]
          exact mul_le_mul_of_nonneg_right (ih (fun i : Fin n => ν i.castSucc) g' hg' hg'diff)
            (Real.exp_pos _).le
      _ = Real.exp ((n + 1 : ℕ) * t ^ 2 * c ^ 2 / 2) := by
          rw [← Real.exp_add]
          congr 1
          push_cast
          ring

/-! ### Conditioning on an independent random element -/

/-- **Freezing lemma.** For independent `Γ`, `X`: `E[F(Γ, X) | Γ] = ∫ F(Γ, x) d(law of X)` a.s. -/
lemma condExp_comap_eq_integral_of_indepFun {Ω G H : Type*} [MeasurableSpace Ω]
    [MeasurableSpace G] [MeasurableSpace H] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {Γ : Ω → G} {X : Ω → H} (hΓ : Measurable Γ) (hX : Measurable X) (hindep : IndepFun Γ X μ)
    {F : G × H → ℝ} (hF : Measurable F) (hint : Integrable (fun ω => F (Γ ω, X ω)) μ) :
    μ[fun ω => F (Γ ω, X ω) | MeasurableSpace.comap Γ inferInstance] =ᵐ[μ]
      fun ω => ∫ x, F (Γ ω, x) ∂μ.map X := by
  -- the law of `(Γ, X)` is a product measure, and `F` is integrable for it
  have hlaw : μ.map (fun ω => (Γ ω, X ω)) = (μ.map Γ).prod (μ.map X) :=
    (indepFun_iff_map_prod_eq_prod_map_map hΓ.aemeasurable hX.aemeasurable).mp hindep
  have hFint : Integrable F ((μ.map Γ).prod (μ.map X)) := by
    rw [← hlaw]
    exact (integrable_map_measure hF.aestronglyMeasurable (hΓ.prodMk hX).aemeasurable).mpr hint
  let ψ : G → ℝ := fun γ => ∫ x, F (γ, x) ∂μ.map X
  have hψm : Measurable ψ := hF.stronglyMeasurable.integral_prod_right'.measurable
  have hψint : Integrable ψ (μ.map Γ) := hFint.integral_prod_left
  -- `ψ ∘ Γ` has the defining properties of the conditional expectation
  symm
  refine ae_eq_condExp_of_forall_setIntegral_eq hΓ.comap_le hint (fun s _ _ => ?_)
    (fun s hs _ => ?_) ?_
  · exact (hψint.comp_measurable hΓ).integrableOn
  · obtain ⟨S, hS, rfl⟩ := hs
    calc ∫ ω in Γ ⁻¹' S, ψ (Γ ω) ∂μ = ∫ γ in S, ψ γ ∂μ.map Γ :=
          (setIntegral_map hS hψm.aestronglyMeasurable hΓ.aemeasurable).symm
      _ = ∫ p in S ×ˢ Set.univ, F p ∂(μ.map Γ).prod (μ.map X) := by
          rw [setIntegral_prod _ hFint.integrableOn]
          simp only [Measure.restrict_univ, ψ]
      _ = ∫ p in S ×ˢ Set.univ, F p ∂μ.map (fun ω => (Γ ω, X ω)) := by rw [hlaw]
      _ = ∫ ω in (fun ω => (Γ ω, X ω)) ⁻¹' (S ×ˢ Set.univ), F (Γ ω, X ω) ∂μ :=
          setIntegral_map (hS.prod MeasurableSet.univ) hF.aestronglyMeasurable
            (hΓ.prodMk hX).aemeasurable
      _ = ∫ ω in Γ ⁻¹' S, F (Γ ω, X ω) ∂μ := by
          congr 2
          ext ω
          simp
  · exact (hψm.comp (comap_measurable Γ)).stronglyMeasurable.aestronglyMeasurable

/-- First step of the proof of Fact A.1: the centered exponential is integrable, and
conditioning on `Γ = γ` amounts to fixing the first argument of `φ`. -/
lemma fact_A_1_freeze {Ω G E : Type*} [MeasurableSpace Ω] [MeasurableSpace G]
    [MeasurableSpace E] {μ : Measure Ω} [IsProbabilityMeasure μ] {n : ℕ}
    (Γ : Ω → G) (ξ : Fin n → Ω → E) (hΓ : Measurable Γ) (hξ : ∀ i, Measurable (ξ i))
    (hξindep : iIndepFun ξ μ)
    (hΓindep : IndepFun Γ (fun ω i => ξ i ω) μ)
    (φ : G × (Fin n → E) → ℝ) (hφ : Measurable φ) {c : ℝ}
    (hdiff : ∀ γ x i a, |φ (γ, Function.update x i a) - φ (γ, x)| ≤ c)
    (hint : Integrable (fun ω => φ (Γ ω, fun i => ξ i ω)) μ)
    (t : ℝ) :
    Integrable (fun ω => Real.exp (t * (φ (Γ ω, fun i => ξ i ω) -
        (μ[fun ω => φ (Γ ω, fun i => ξ i ω) | MeasurableSpace.comap Γ inferInstance]) ω))) μ ∧
      μ[fun ω => Real.exp (t * (φ (Γ ω, fun i => ξ i ω) -
            (μ[fun ω => φ (Γ ω, fun i => ξ i ω) |
              MeasurableSpace.comap Γ inferInstance]) ω)) |
          MeasurableSpace.comap Γ inferInstance] =ᵐ[μ]
        fun ω => ∫ x, Real.exp (t * (φ (Γ ω, x) -
          ∫ y, φ (Γ ω, y) ∂Measure.pi fun i => μ.map (ξ i))) ∂Measure.pi fun i => μ.map (ξ i) := by
  -- `X = (ξ_1, …, ξ_n)`; its law is the product of the laws of the `ξ_i`
  let X : Ω → (Fin n → E) := fun ω i => ξ i ω
  have hXm : Measurable X := measurable_pi_iff.mpr hξ
  have hlawX : Measure.pi (fun i => μ.map (ξ i)) = μ.map X :=
    ((iIndepFun_iff_map_fun_eq_pi_map (fun i => (hξ i).aemeasurable)).mp hξindep).symm
  rw [hlawX]
  haveI : IsProbabilityMeasure (μ.map X) := Measure.isProbabilityMeasure_map hXm.aemeasurable
  -- the sections `φ (γ, ·)` have oscillation at most `n c`, and `ψ γ` is their mean
  have hosc : ∀ γ x y, |φ (γ, x) - φ (γ, y)| ≤ n * c := fun γ =>
    abs_sub_le_of_bounded_differences (fun x => φ (γ, x)) (hdiff γ)
  let ψ : G → ℝ := fun γ => ∫ x, φ (γ, x) ∂μ.map X
  have hψm : Measurable ψ := hφ.stronglyMeasurable.integral_prod_right'.measurable
  have hcenter : ∀ γ x, |φ (γ, x) - ψ γ| ≤ n * c := fun γ =>
    abs_sub_integral_le (integrable_of_abs_sub_le (hφ.comp measurable_prodMk_left) (hosc γ))
      (hosc γ)
  -- `E[f | Γ] = ψ(Γ)` almost surely
  have hA : μ[fun ω => φ (Γ ω, X ω) | MeasurableSpace.comap Γ inferInstance] =ᵐ[μ]
      fun ω => ψ (Γ ω) :=
    condExp_comap_eq_integral_of_indepFun hΓ hXm hΓindep hφ hint
  -- the centered exponential is a bounded function `F` of the values of `Γ` and `X`
  let F : G × (Fin n → E) → ℝ := fun p => Real.exp (t * (φ p - ψ p.1))
  have hFm : Measurable F :=
    Real.measurable_exp.comp ((hφ.sub (hψm.comp measurable_fst)).const_mul t)
  have hFint : Integrable (fun ω => F (Γ ω, X ω)) μ := by
    refine Integrable.of_bound (hFm.comp (hΓ.prodMk hXm)).aestronglyMeasurable
      (Real.exp (|t| * (n * c))) (Filter.Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    apply Real.exp_le_exp.mpr
    calc t * (φ (Γ ω, X ω) - ψ (Γ ω)) ≤ |t * (φ (Γ ω, X ω) - ψ (Γ ω))| := le_abs_self _
      _ = |t| * |φ (Γ ω, X ω) - ψ (Γ ω)| := abs_mul _ _
      _ ≤ |t| * (n * c) := mul_le_mul_of_nonneg_left (hcenter _ _) (abs_nonneg t)
  have hB : (fun ω => Real.exp (t * (φ (Γ ω, fun i => ξ i ω) -
      (μ[fun ω => φ (Γ ω, fun i => ξ i ω) | MeasurableSpace.comap Γ inferInstance]) ω)))
      =ᵐ[μ] fun ω => F (Γ ω, X ω) := by
    filter_upwards [hA] with ω hω
    rw [hω]
  -- freeze `Γ` in `F`
  exact ⟨hFint.congr hB.symm, (condExp_congr_ae hB).trans
    (condExp_comap_eq_integral_of_indepFun hΓ hXm hΓindep hFm hFint)⟩

/-- In the setting of Fact A.1, the exponential `exp(t (f - E[f | Γ]))` is integrable. -/
theorem fact_A_1_integrable {Ω G E : Type*} [MeasurableSpace Ω] [MeasurableSpace G]
    [MeasurableSpace E] {μ : Measure Ω} [IsProbabilityMeasure μ] {n : ℕ}
    (Γ : Ω → G) (ξ : Fin n → Ω → E) (hΓ : Measurable Γ) (hξ : ∀ i, Measurable (ξ i))
    (hξindep : iIndepFun ξ μ)
    (hΓindep : IndepFun Γ (fun ω i => ξ i ω) μ)
    (φ : G × (Fin n → E) → ℝ) (hφ : Measurable φ) {c : ℝ}
    (hdiff : ∀ γ x i a, |φ (γ, Function.update x i a) - φ (γ, x)| ≤ c)
    (hint : Integrable (fun ω => φ (Γ ω, fun i => ξ i ω)) μ)
    (t : ℝ) :
    Integrable (fun ω => Real.exp (t * (φ (Γ ω, fun i => ξ i ω) -
        (μ[fun ω => φ (Γ ω, fun i => ξ i ω) | MeasurableSpace.comap Γ inferInstance]) ω))) μ :=
  (fact_A_1_freeze Γ ξ hΓ hξ hξindep hΓindep φ hφ hdiff hint t).1

/-- **Fact A.1 (bounded differences).** Let `ξ_1, …, ξ_n` be independent random variables with
values in a measurable space `E`, and let `Γ` be a random element of a measurable space `G`,
independent of `(ξ_1, …, ξ_n)`. Let `f = φ(Γ, ξ_1, …, ξ_n)` be integrable, where `φ` is
measurable and, for every `γ`, changing one of the last `n` arguments changes `φ(γ, ·)` by at
most `c > 0`. Then for every real `t`, almost surely

`E[exp(t (f - E[f | Γ])) | Γ] ≤ exp(n t² c² / 2)`. -/
theorem fact_A_1 {Ω G E : Type*} [MeasurableSpace Ω] [MeasurableSpace G] [MeasurableSpace E]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {n : ℕ}
    (Γ : Ω → G) (ξ : Fin n → Ω → E) (hΓ : Measurable Γ) (hξ : ∀ i, Measurable (ξ i))
    (hξindep : iIndepFun ξ μ)
    (hΓindep : IndepFun Γ (fun ω i => ξ i ω) μ)
    (φ : G × (Fin n → E) → ℝ) (hφ : Measurable φ)
    {c : ℝ} (hc : 0 < c)
    (hdiff : ∀ γ x i a, |φ (γ, Function.update x i a) - φ (γ, x)| ≤ c)
    (hint : Integrable (fun ω => φ (Γ ω, fun i => ξ i ω)) μ)
    (t : ℝ) :
    ∀ᵐ ω ∂μ,
      (μ[fun ω => Real.exp (t * (φ (Γ ω, fun i => ξ i ω) -
            (μ[fun ω => φ (Γ ω, fun i => ξ i ω) |
              MeasurableSpace.comap Γ inferInstance]) ω)) |
          MeasurableSpace.comap Γ inferInstance]) ω ≤
        Real.exp (n * t ^ 2 * c ^ 2 / 2) := by
  -- conditioning on `Γ = γ` fixes the first argument of `φ`; then the unconditional bound
  filter_upwards [(fact_A_1_freeze Γ ξ hΓ hξ hξindep hΓindep φ hφ hdiff hint t).2] with ω hω
  rw [hω]
  haveI : ∀ i, IsProbabilityMeasure (μ.map (ξ i)) := fun i =>
    Measure.isProbabilityMeasure_map (hξ i).aemeasurable
  exact bounded_differences_pi (fun i => μ.map (ξ i)) (fun x => φ (Γ ω, x))
    (hφ.comp measurable_prodMk_left) hc.le (hdiff (Γ ω)) t

end

end R56Audit
end

section
open MeasureTheory ProbabilityTheory

namespace TusnadyPlane.RandomPoints

theorem chk_fact_A_1 {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (n : ℕ) {B : Type*} [MeasurableSpace B]
    {E : Fin n → Type*} [∀ i, MeasurableSpace (E i)]
    (Γ : Ω → B) (ξ : (i : Fin n) → Ω → E i)
    (hΓ : Measurable Γ) (hξ : ∀ i, Measurable (ξ i))
    (hind : iIndepFun ξ μ) (hbackground : IndepFun Γ (fun ω i => ξ i ω) μ)
    (φ : B × ((i : Fin n) → E i) → ℝ) (hφ : Measurable φ)
    (hint : Integrable (fun ω => φ (Γ ω, fun i => ξ i ω)) μ)
    (c : ℝ) (hc : 0 < c)
    (hchange : ∀ (γ : B) (x y : (i : Fin n) → E i) (i : Fin n),
      (∀ k, k ≠ i → x k = y k) → |φ (γ,x) - φ (γ,y)| ≤ c) (t : ℝ) :
    let f := fun ω => φ (Γ ω, fun i => ξ i ω)
    let H := MeasurableSpace.comap Γ inferInstance
    Integrable (fun ω => Real.exp (t * (f ω - condExp H μ f ω))) μ ∧
    ∀ᵐ ω ∂μ,
      condExp H μ (fun v => Real.exp (t * (f v - condExp H μ f v))) ω ≤
        Real.exp ((n : ℝ)*t^2*c^2/2) := by
  intro f
  dsimp only
  classical
  obtain ⟨ω0⟩ : Nonempty Ω := by
    by_contra h
    rw [not_nonempty_iff] at h
    have := measure_univ (μ := μ)
    rw [Set.univ_eq_empty_iff.mpr h, measure_empty] at this
    exact zero_ne_one this
  -- embed the coordinates into the full product `Π j, E j`
  let g : (i : Fin n) → E i → ((j : Fin n) → E j) :=
    fun i e => Function.update (fun j => ξ j ω0) i e
  have hg : ∀ i, Measurable (g i) := by
    intro i
    refine measurable_pi_iff.mpr fun j => ?_
    by_cases hji : j = i
    · subst hji
      simp only [g, Function.update_self]
      exact measurable_id
    · simp only [g, Function.update_of_ne hji]
      exact measurable_const
  let ξ' : Fin n → Ω → ((j : Fin n) → E j) := fun i ω => g i (ξ i ω)
  have hξ' : ∀ i, Measurable (ξ' i) := fun i => (hg i).comp (hξ i)
  have hind' : iIndepFun ξ' μ := hind.comp g hg
  let G : (Fin n → ((j : Fin n) → E j)) → ((i : Fin n) → E i) := fun x i => x i i
  have hG : Measurable G :=
    measurable_pi_iff.mpr fun i => (measurable_pi_apply i).comp (measurable_pi_apply i)
  let ι : ((i : Fin n) → E i) → (Fin n → ((j : Fin n) → E j)) := fun x i => g i (x i)
  have hι : Measurable ι :=
    measurable_pi_iff.mpr fun i => (hg i).comp (measurable_pi_apply i)
  have hbg' : IndepFun Γ (fun ω i => ξ' i ω) μ :=
    hbackground.comp measurable_id hι
  let φ' : B × (Fin n → ((j : Fin n) → E j)) → ℝ := fun p => φ (p.1, G p.2)
  have hφ' : Measurable φ' := hφ.comp (measurable_fst.prodMk (hG.comp measurable_snd))
  have hGξ : ∀ ω, G (fun i => ξ' i ω) = fun i => ξ i ω := by
    intro ω; funext i; simp [G, ξ', g]
  have hf' : (fun ω => φ' (Γ ω, fun i => ξ' i ω)) = f := by
    funext ω; simp [φ', hGξ, f]
  have hint' : Integrable (fun ω => φ' (Γ ω, fun i => ξ' i ω)) μ := by rw [hf']; exact hint
  have hdiff : ∀ γ x i a, |φ' (γ, Function.update x i a) - φ' (γ, x)| ≤ c := by
    intro γ x i a
    refine hchange γ _ _ i fun k hk => ?_
    simp [G, Function.update_of_ne hk]
  have h1 := R56Audit.fact_A_1_integrable Γ ξ' hΓ hξ' hind' hbg' φ' hφ' hdiff hint' t
  have h2 := R56Audit.fact_A_1 Γ ξ' hΓ hξ' hind' hbg' φ' hφ' hc hdiff hint' t
  have e : ∀ ω, φ' (Γ ω, fun i => ξ' i ω) = f ω := fun ω => congrFun hf' ω
  simp only [e] at h1 h2
  exact ⟨h1, h2⟩

end TusnadyPlane.RandomPoints
end

theorem solution : type_of% @TusnadyPlane.RandomPoints.chk_fact_A_1 := @TusnadyPlane.RandomPoints.chk_fact_A_1
