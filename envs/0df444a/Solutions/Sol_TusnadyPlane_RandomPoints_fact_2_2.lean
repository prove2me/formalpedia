-- Prove2me | solution 1 for TusnadyPlane.RandomPoints.fact_2_2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T16:28:31.185179+00:00
-- url     : https://prove2.me/submissions/7a272057-6a71-4918-afcf-ab9b9bee835b

import Mathlib.Probability.Moments.SubGaussian
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Tactic

section
/-!
# Fact 2.2 of the manuscript (sums of symmetric variables), for real random variables

Auditor's supplement (not part of the audited archive).

**Fact 2.2.** Let `X_1, …, X_m` be independent symmetric random variables. Suppose that
`E X_i² = σ²` and `E X_i⁴ ≤ 3σ⁴` for every `i`, where `σ > 0`. Then
`E|θ + X_1 + ⋯ + X_m| ≥ σ √(m/3)` for every real `θ`.

Symmetric variables are "variables that have the same distribution as their negatives": the
hypothesis on `X_i` is `IdentDistrib (X i) (fun ω => -X i ω) μ μ`. The proof is the one of
Appendix A.1: the shift does not hurt; two moments; from moments to the absolute value
(Hölder with exponents `3/2` and `3`).

`fact_2_2_general` is the statement for random variables on an arbitrary probability space.
(`fact_2_2_uniform` in `UniformDigits.lean` is the special case of functions of independent
uniform digits, which is the form in which Lemma 2.3 uses the fact.) This file uses Mathlib
only, not the archive.

The three steps of Appendix A.1, with `X = Σ_i X_i`:

* the shift does not hurt: `identDistrib_sum_neg` (`X` and `-X` have the same distribution),
  `integral_abs_add_eq_integral_abs_sub` (`E|θ + X| = E|θ - X|`) and
  `integral_abs_le_integral_abs_add_of_symm` (`E|θ + X| ≥ E|X|`);
* two moments: `integral_pow_eq_zero_of_symm` (`E X_i = 0`, and also `E X_i³ = 0`),
  `sum_moments` (`E X² = mσ²` and `E X⁴ = Σ_i E X_i⁴ + 3m(m-1)σ⁴`) and `sum_fourth_moment_le`
  (`E X⁴ ≤ 3m²σ⁴`). The proof of `sum_moments` is by induction on the number of variables
  (one variable is added at a time, with `moments_add_of_indepFun`), not by expanding `X⁴`
  and counting the surviving terms as the manuscript does. The manuscript's term
  `6 Σ_{i<j} E X_i² E X_j²` appears in the evaluated form `3m(m-1)σ⁴`, which is the same
  number because every `E X_i² = σ²` and there are `m(m-1)/2` pairs `i < j`;
* from moments to the absolute value: `integral_sq_le_rpow_mul_rpow` (Hölder's inequality,
  `E X² ≤ (E|X|)^{2/3} (E X⁴)^{1/3}`), `integral_sq_pow_three_le` (its cube,
  `(E X²)³ ≤ (E|X|)² E X⁴`) and `mul_sqrt_le_of_moments` (the arithmetic).
-/

namespace R56Audit

open MeasureTheory ProbabilityTheory

noncomputable section

section General

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-! ### The shift does not hurt -/

/-- Independent symmetric variables are jointly symmetric: the families `(X_i)` and `(-X_i)`
have the same joint law, namely the product of the common marginal laws. -/
lemma identDistrib_neg_of_iIndepFun {ι : Type*} [Fintype ι] (X : ι → Ω → ℝ)
    (hindep : iIndepFun X μ) (hsymm : ∀ i, IdentDistrib (X i) (fun ω => -X i ω) μ μ) :
    IdentDistrib (fun ω i => X i ω) (fun ω i => -X i ω) μ μ := by
  have hX : ∀ i, AEMeasurable (X i) μ := fun i => (hsymm i).aemeasurable_fst
  have hnX : ∀ i, AEMeasurable (fun ω => -X i ω) μ := fun i => (hsymm i).aemeasurable_snd
  have hneg : iIndepFun (fun i ω => -X i ω) μ :=
    hindep.comp (fun _ x => -x) fun _ => measurable_neg
  refine ⟨aemeasurable_pi_iff.mpr hX, aemeasurable_pi_iff.mpr hnX, ?_⟩
  rw [hindep.map_fun_eq_pi_map hX, hneg.map_fun_eq_pi_map hnX]
  congr 1
  funext i
  exact (hsymm i).map_eq

/-- A finite sum `X` of independent symmetric variables is symmetric: `X` and `-X` have the
same distribution. -/
lemma identDistrib_sum_neg {ι : Type*} [Fintype ι] (X : ι → Ω → ℝ)
    (hindep : iIndepFun X μ) (hsymm : ∀ i, IdentDistrib (X i) (fun ω => -X i ω) μ μ) :
    IdentDistrib (fun ω => ∑ i, X i ω) (fun ω => -∑ i, X i ω) μ μ := by
  have hsum : Measurable fun v : ι → ℝ => ∑ i, v i :=
    Finset.measurable_fun_sum _ fun i _ => measurable_pi_apply i
  have h := (identDistrib_neg_of_iIndepFun X hindep hsymm).comp hsum
  simpa only [Function.comp_def, Finset.sum_neg_distrib] using h

/-- **The shift does not hurt**, the equality (Appendix A.1): "So `X` and `-X` have the same
distribution, and `E|θ + X| = E|θ - X|`." The lemma is the second half of this sentence, for
a real random variable `X` that has the same distribution as `-X`. (The first half, for
`X = Σ_i X_i`, is `identDistrib_sum_neg`.) No integrability hypothesis is needed, because
identically distributed functions have the same integral (`IdentDistrib.integral_eq`). -/
lemma integral_abs_add_eq_integral_abs_sub {X : Ω → ℝ}
    (hsymm : IdentDistrib X (fun ω => -X ω) μ μ) (θ : ℝ) :
    ∫ ω, |θ + X ω| ∂μ = ∫ ω, |θ - X ω| ∂μ := by
  -- apply the measurable function `x ↦ |θ + x|` to `X` and to `-X`
  have hg : Measurable fun x : ℝ => |θ + x| :=
    (continuous_const.add continuous_id).abs.measurable
  have h := (hsymm.comp hg).integral_eq
  simpa only [Function.comp_def, sub_eq_add_neg] using h

/-- **The shift does not hurt** (Appendix A.1): `E|θ + X| ≥ E|X|` for a symmetric integrable
variable `X`. "Averaging the two and using `|θ + x| + |θ - x| ≥ 2|x|` gives
`E|θ + X| ≥ E|X|`." The two are `E|θ + X|` and `E|θ - X|`, which are equal by
`integral_abs_add_eq_integral_abs_sub`. -/
lemma integral_abs_le_integral_abs_add_of_symm [IsFiniteMeasure μ] {X : Ω → ℝ}
    (hsymm : IdentDistrib X (fun ω => -X ω) μ μ) (hX : Integrable X μ) (θ : ℝ) :
    ∫ ω, |X ω| ∂μ ≤ ∫ ω, |θ + X ω| ∂μ := by
  have hp : Integrable (fun ω => |θ + X ω|) μ := ((integrable_const θ).add hX).abs
  have hm : Integrable (fun ω => |θ - X ω|) μ := ((integrable_const θ).sub hX).abs
  -- `|θ + x| + |θ - x| ≥ 2|x|`, by the triangle inequality
  have hpoint : ∀ ω, |X ω| ≤ (|θ + X ω| + |θ - X ω|) / 2 := by
    intro ω
    have h := abs_sub (θ + X ω) (θ - X ω)
    have e : θ + X ω - (θ - X ω) = 2 * X ω := by ring
    rw [e, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)] at h
    linarith
  -- average `E|θ + X|` and `E|θ - X|`, which are equal
  calc ∫ ω, |X ω| ∂μ ≤ ∫ ω, (|θ + X ω| + |θ - X ω|) / 2 ∂μ :=
        integral_mono hX.abs ((hp.add hm).div_const 2) hpoint
    _ = (∫ ω, |θ + X ω| ∂μ + ∫ ω, |θ - X ω| ∂μ) / 2 := by
        rw [integral_div, integral_add hp hm]
    _ = ∫ ω, |θ + X ω| ∂μ := by
        rw [← integral_abs_add_eq_integral_abs_sub hsymm θ]
        ring

/-! ### Two moments -/

/-- A symmetric real random variable has vanishing odd moments: `E Y^k = 0` for odd `k`.

The case `k = 1` is the mean, because `Y ω ^ 1` is `Y ω` (`pow_one`). So this lemma covers
the manuscript's "Every `X_i` is symmetric and has a finite second moment, so `E X_i = 0`",
and there is no separate lemma for the mean; `sum_moments` uses the cases `k = 1` and
`k = 3`. No moment hypothesis is needed: if `Y ^ k` is not integrable, then its integral is
`0` by Mathlib's convention. -/
lemma integral_pow_eq_zero_of_symm {Y : Ω → ℝ} (h : IdentDistrib Y (fun ω => -Y ω) μ μ) {k : ℕ}
    (hk : Odd k) : ∫ ω, Y ω ^ k ∂μ = 0 := by
  have h1 := (h.comp (measurable_id.pow_const k)).integral_eq
  simp only [Function.comp_apply, id_eq, hk.neg_pow, integral_neg] at h1
  linarith

/-- On a finite measure space, a real function with an integrable fourth power has integrable
lower powers. -/
lemma integrable_pow_of_integrable_pow_four [IsFiniteMeasure μ] {Y : Ω → ℝ}
    (hY : AEMeasurable Y μ) (h4 : Integrable (fun ω => Y ω ^ 4) μ) {k : ℕ} (hk : k ≤ 4) :
    Integrable (fun ω => Y ω ^ k) μ := by
  have h4' : Integrable (fun ω => ‖Y ω‖ ^ 4) μ := by
    simpa only [Real.norm_eq_abs, (by decide : Even 4).pow_abs] using h4
  have hk' := integrable_norm_pow_of_le hY.aestronglyMeasurable hk h4'
  refine (integrable_norm_iff (hY.pow_const k).aestronglyMeasurable).mp ?_
  simpa only [norm_pow] using hk'

/-- **Two moments, one step.** Let `Y` and `T` be independent with finite fourth moments, and
let `E Y = E Y³ = 0`. Then `(Y + T)⁴` is integrable, `E (Y + T)² = E Y² + E T²` and
`E (Y + T)⁴ = E Y⁴ + 6 E Y² E T² + E T⁴`. -/
lemma moments_add_of_indepFun [IsFiniteMeasure μ] {Y T : Ω → ℝ} (hYT : IndepFun Y T μ)
    (hY : AEMeasurable Y μ) (hT : AEMeasurable T μ)
    (hY4 : Integrable (fun ω => Y ω ^ 4) μ) (hT4 : Integrable (fun ω => T ω ^ 4) μ)
    (hY1 : ∫ ω, Y ω ∂μ = 0) (hY3 : ∫ ω, Y ω ^ 3 ∂μ = 0) :
    Integrable (fun ω => (Y ω + T ω) ^ 4) μ ∧
      ∫ ω, (Y ω + T ω) ^ 2 ∂μ = ∫ ω, Y ω ^ 2 ∂μ + ∫ ω, T ω ^ 2 ∂μ ∧
      ∫ ω, (Y ω + T ω) ^ 4 ∂μ =
        ∫ ω, Y ω ^ 4 ∂μ + 6 * ((∫ ω, Y ω ^ 2 ∂μ) * ∫ ω, T ω ^ 2 ∂μ) + ∫ ω, T ω ^ 4 ∂μ := by
  -- the mixed moments `E(Y^a T^b)` are finite and factor
  have hint : ∀ a b : ℕ, a ≤ 4 → b ≤ 4 → Integrable (fun ω => Y ω ^ a * T ω ^ b) μ :=
    fun a b ha hb =>
      (hYT.comp (measurable_id.pow_const a) (measurable_id.pow_const b)).integrable_mul
        (integrable_pow_of_integrable_pow_four hY hY4 ha)
        (integrable_pow_of_integrable_pow_four hT hT4 hb)
  have hfac : ∀ a b : ℕ, ∫ ω, Y ω ^ a * T ω ^ b ∂μ = (∫ ω, Y ω ^ a ∂μ) * ∫ ω, T ω ^ b ∂μ :=
    fun a b => hYT.integral_fun_comp_mul_comp hY hT
      (measurable_id.pow_const a).aestronglyMeasurable
      (measurable_id.pow_const b).aestronglyMeasurable
  have hY1' : ∫ ω, Y ω ^ 1 ∂μ = 0 := by simpa only [pow_one] using hY1
  have hY2 := integrable_pow_of_integrable_pow_four hY hY4 (k := 2) (by norm_num)
  have hT2 := integrable_pow_of_integrable_pow_four hT hT4 (k := 2) (by norm_num)
  have i11 := (hint 1 1 (by norm_num) (by norm_num)).const_mul 2
  have i31 := (hint 3 1 (by norm_num) (by norm_num)).const_mul 4
  have i22 := (hint 2 2 (by norm_num) (by norm_num)).const_mul 6
  have i13 := (hint 1 3 (by norm_num) (by norm_num)).const_mul 4
  -- the binomial expansions, with every mixed term in the form `Y ^ a * T ^ b`
  have e2 : (fun ω => (Y ω + T ω) ^ 2) =
      fun ω => Y ω ^ 2 + 2 * (Y ω ^ 1 * T ω ^ 1) + T ω ^ 2 := by
    funext ω
    ring
  have e4 : (fun ω => (Y ω + T ω) ^ 4) = fun ω => Y ω ^ 4 + 4 * (Y ω ^ 3 * T ω ^ 1) +
      6 * (Y ω ^ 2 * T ω ^ 2) + 4 * (Y ω ^ 1 * T ω ^ 3) + T ω ^ 4 := by
    funext ω
    ring
  have s1 : Integrable (fun ω => Y ω ^ 2 + 2 * (Y ω ^ 1 * T ω ^ 1)) μ := hY2.add i11
  have t1 : Integrable (fun ω => Y ω ^ 4 + 4 * (Y ω ^ 3 * T ω ^ 1)) μ := hY4.add i31
  have t2 : Integrable (fun ω => Y ω ^ 4 + 4 * (Y ω ^ 3 * T ω ^ 1) +
      6 * (Y ω ^ 2 * T ω ^ 2)) μ := t1.add i22
  have t3 : Integrable (fun ω => Y ω ^ 4 + 4 * (Y ω ^ 3 * T ω ^ 1) +
      6 * (Y ω ^ 2 * T ω ^ 2) + 4 * (Y ω ^ 1 * T ω ^ 3)) μ := t2.add i13
  refine ⟨?_, ?_, ?_⟩
  · rw [e4]
    exact t3.add hT4
  · rw [e2, integral_add s1 hT2, integral_add hY2 i11, integral_const_mul, hfac, hY1']
    ring
  · rw [e4, integral_add t3 hT4, integral_add t2 i13, integral_add t1 i22, integral_add hY4 i31,
      integral_const_mul, integral_const_mul, integral_const_mul, hfac 3 1, hfac 2 2, hfac 1 3,
      hY1', hY3]
    ring

/-- **Two moments** (Appendix A.1). For independent symmetric variables with `E X_i² = σ²` and
finite fourth moments, the sum `X` over a set of `m` indices has a finite fourth moment,
`E X² = mσ²` and `E X⁴ = Σ_i E X_i⁴ + 3m(m-1)σ⁴`.

The proof is by induction on the number of variables (one variable is added at a time, with
`moments_add_of_indepFun`), not by expanding `X⁴` and counting the surviving terms as the
manuscript does. The manuscript's term `6 Σ_{i<j} E X_i² E X_j²` appears here in the
evaluated form `3m(m-1)σ⁴`, which is the same number because every `E X_i² = σ²` and there
are `m(m-1)/2` pairs `i < j`. -/
lemma sum_moments [IsProbabilityMeasure μ] {ι : Type*} (X : ι → Ω → ℝ)
    (hindep : iIndepFun X μ) (hsymm : ∀ i, IdentDistrib (X i) (fun ω => -X i ω) μ μ) {σ : ℝ}
    (h2 : ∀ i, ∫ ω, X i ω ^ 2 ∂μ = σ ^ 2) (h4i : ∀ i, Integrable (fun ω => X i ω ^ 4) μ)
    (s : Finset ι) :
    Integrable (fun ω => (∑ i ∈ s, X i ω) ^ 4) μ ∧
      ∫ ω, (∑ i ∈ s, X i ω) ^ 2 ∂μ = s.card * σ ^ 2 ∧
      ∫ ω, (∑ i ∈ s, X i ω) ^ 4 ∂μ =
        ∑ i ∈ s, ∫ ω, X i ω ^ 4 ∂μ + 3 * s.card * (s.card - 1) * σ ^ 4 := by
  classical
  have hX : ∀ i, AEMeasurable (X i) μ := fun i => (hsymm i).aemeasurable_fst
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    obtain ⟨ihi, ih2, ih4⟩ := ih
    have hT : AEMeasurable (fun ω => ∑ j ∈ s, X j ω) μ :=
      Finset.aemeasurable_fun_sum s fun j _ => hX j
    -- the new variable is independent of the partial sum
    have hYT : IndepFun (X i) (fun ω => ∑ j ∈ s, X j ω) μ := by
      have h := (hindep.indepFun_finsetSum_of_notMem₀ hX hi).symm
      have e : (∑ j ∈ s, X j) = fun ω => ∑ j ∈ s, X j ω := by
        funext ω
        simp
      rwa [e] at h
    -- its odd moments vanish by symmetry
    obtain ⟨hi4, hm2, hm4⟩ := moments_add_of_indepFun hYT (hX i) hT (h4i i) ihi
      (by simpa using integral_pow_eq_zero_of_symm (hsymm i) (k := 1) (by decide))
      (integral_pow_eq_zero_of_symm (hsymm i) (by decide))
    simp only [Finset.sum_insert hi]
    refine ⟨hi4, ?_, ?_⟩
    · rw [hm2, h2 i, ih2, Finset.card_insert_of_notMem hi]
      push_cast
      ring
    · rw [hm4, h2 i, ih2, ih4, Finset.card_insert_of_notMem hi]
      push_cast
      ring

/-- **Two moments** (Appendix A.1), the bound on the fourth moment: if moreover
`E X_i⁴ ≤ 3σ⁴`, then `E X⁴ ≤ 3mσ⁴ + 3m(m-1)σ⁴ = 3m²σ⁴`. -/
lemma sum_fourth_moment_le [IsProbabilityMeasure μ] {ι : Type*} (X : ι → Ω → ℝ)
    (hindep : iIndepFun X μ) (hsymm : ∀ i, IdentDistrib (X i) (fun ω => -X i ω) μ μ) {σ : ℝ}
    (h2 : ∀ i, ∫ ω, X i ω ^ 2 ∂μ = σ ^ 2) (h4i : ∀ i, Integrable (fun ω => X i ω ^ 4) μ)
    (h4 : ∀ i, ∫ ω, X i ω ^ 4 ∂μ ≤ 3 * σ ^ 4) (s : Finset ι) :
    ∫ ω, (∑ i ∈ s, X i ω) ^ 4 ∂μ ≤ 3 * (s.card * σ ^ 2) ^ 2 := by
  have hsum : ∑ i ∈ s, ∫ ω, X i ω ^ 4 ∂μ ≤ s.card * (3 * σ ^ 4) := by
    simpa only [nsmul_eq_mul] using Finset.sum_le_card_nsmul s _ _ fun i _ => h4 i
  rw [(sum_moments X hindep hsymm h2 h4i s).2.2]
  linarith

/-! ### From moments to the absolute value -/

/-- **Hölder's inequality with exponents `3/2` and `3`** (Appendix A.1), applied to the factors
`|Y|^{2/3}` and `|Y|^{4/3}`: `E Y² ≤ (E|Y|)^{2/3} (E Y⁴)^{1/3}`. -/
lemma integral_sq_le_rpow_mul_rpow [IsFiniteMeasure μ] {Y : Ω → ℝ} (hY : AEMeasurable Y μ)
    (h4 : Integrable (fun ω => Y ω ^ 4) μ) :
    ∫ ω, Y ω ^ 2 ∂μ ≤ (∫ ω, |Y ω| ∂μ) ^ (2 / 3 : ℝ) * (∫ ω, Y ω ^ 4 ∂μ) ^ (1 / 3 : ℝ) := by
  have hpq : (3 / 2 : ℝ).HolderConjugate 3 := by norm_num [Real.holderConjugate_iff]
  have habs : AEMeasurable (fun ω => |Y ω|) μ := continuous_abs.measurable.comp_aemeasurable hY
  have h1 : Integrable (fun ω => |Y ω|) μ := by
    simpa only [pow_one] using
      (integrable_pow_of_integrable_pow_four hY h4 (k := 1) (by norm_num)).abs
  -- the two factors are nonnegative, their product is `Y²`
  have hf0 : ∀ ω, 0 ≤ |Y ω| ^ (2 / 3 : ℝ) := fun ω => Real.rpow_nonneg (abs_nonneg _) _
  have hg0 : ∀ ω, 0 ≤ |Y ω| ^ (4 / 3 : ℝ) := fun ω => Real.rpow_nonneg (abs_nonneg _) _
  have hfg : ∀ ω, |Y ω| ^ (2 / 3 : ℝ) * |Y ω| ^ (4 / 3 : ℝ) = Y ω ^ 2 := fun ω => by
    rw [← Real.rpow_add_of_nonneg (abs_nonneg _) (by norm_num) (by norm_num), ← sq_abs,
      ← Real.rpow_natCast]
    norm_num
  -- the first factor to the power `3/2` is `|Y|`, the second to the power `3` is `Y⁴`
  have hfp : ∀ ω, (|Y ω| ^ (2 / 3 : ℝ)) ^ (3 / 2 : ℝ) = |Y ω| := fun ω => by
    rw [← Real.rpow_mul (abs_nonneg _)]
    norm_num
  have hgq : ∀ ω, (|Y ω| ^ (4 / 3 : ℝ)) ^ (3 : ℝ) = Y ω ^ 4 := fun ω => by
    rw [← Real.rpow_mul (abs_nonneg _), ← (by decide : Even 4).pow_abs, ← Real.rpow_natCast]
    norm_num
  have hfm : MemLp (fun ω => |Y ω| ^ (2 / 3 : ℝ)) (ENNReal.ofReal (3 / 2)) μ := by
    rw [← integrable_norm_rpow_iff (habs.pow_const _).aestronglyMeasurable (by norm_num)
      (by simp), ENNReal.toReal_ofReal (by norm_num)]
    simpa only [Real.norm_of_nonneg (hf0 _), hfp] using h1
  have hgm : MemLp (fun ω => |Y ω| ^ (4 / 3 : ℝ)) (ENNReal.ofReal 3) μ := by
    rw [← integrable_norm_rpow_iff (habs.pow_const _).aestronglyMeasurable (by norm_num)
      (by simp), ENNReal.toReal_ofReal (by norm_num)]
    simpa only [Real.norm_of_nonneg (hg0 _), hgq] using h4
  have h := integral_mul_le_Lp_mul_Lq_of_nonneg hpq (Filter.Eventually.of_forall hf0)
    (Filter.Eventually.of_forall hg0) hfm hgm
  simp only [hfg, hfp, hgq] at h
  rwa [show (1 / (3 / 2) : ℝ) = 2 / 3 by norm_num] at h

/-- **From moments to the absolute value** (Appendix A.1): the cube of Hölder's inequality,
`(E Y²)³ ≤ (E|Y|)² E Y⁴`, in other words `E|Y| ≥ (E Y²)^{3/2} / (E Y⁴)^{1/2}`. -/
lemma integral_sq_pow_three_le [IsFiniteMeasure μ] {Y : Ω → ℝ} (hY : AEMeasurable Y μ)
    (h4 : Integrable (fun ω => Y ω ^ 4) μ) :
    (∫ ω, Y ω ^ 2 ∂μ) ^ 3 ≤ (∫ ω, |Y ω| ∂μ) ^ 2 * ∫ ω, Y ω ^ 4 ∂μ := by
  have hA : 0 ≤ ∫ ω, |Y ω| ∂μ := integral_nonneg fun ω => abs_nonneg _
  have hQ : 0 ≤ ∫ ω, Y ω ^ 4 ∂μ := integral_nonneg fun ω => by positivity
  have hV : 0 ≤ ∫ ω, Y ω ^ 2 ∂μ := integral_nonneg fun ω => sq_nonneg _
  calc (∫ ω, Y ω ^ 2 ∂μ) ^ 3
      ≤ ((∫ ω, |Y ω| ∂μ) ^ (2 / 3 : ℝ) * (∫ ω, Y ω ^ 4 ∂μ) ^ (1 / 3 : ℝ)) ^ 3 :=
        pow_le_pow_left₀ hV (integral_sq_le_rpow_mul_rpow hY h4) 3
    _ = (∫ ω, |Y ω| ∂μ) ^ 2 * ∫ ω, Y ω ^ 4 ∂μ := by
        rw [mul_pow, ← Real.rpow_natCast (_ ^ (2 / 3 : ℝ)) 3, ← Real.rpow_mul hA,
          ← Real.rpow_natCast (_ ^ (1 / 3 : ℝ)) 3, ← Real.rpow_mul hQ]
        norm_num

end General

/-- The arithmetic at the end of Appendix A.1, with `A = E|X|` and `Q = E X⁴`: if
`(mσ²)³ ≤ A² Q` and `Q ≤ 3(mσ²)²`, then `A ≥ σ √(m/3)`. -/
lemma mul_sqrt_le_of_moments {m σ A Q : ℝ} (hm : 0 ≤ m) (hσ : 0 < σ) (hA : 0 ≤ A)
    (h2 : (m * σ ^ 2) ^ 3 ≤ A ^ 2 * Q) (h4 : Q ≤ 3 * (m * σ ^ 2) ^ 2) :
    σ * Real.sqrt (m / 3) ≤ A := by
  have hkey : σ ^ 2 * (m / 3) ≤ A ^ 2 := by
    -- the claim is trivial for `m = 0`; for `m > 0` divide by `3m²σ⁴ > 0`
    rcases hm.eq_or_lt with rfl | hpos
    · rw [zero_div, mul_zero]
      exact sq_nonneg A
    · have hc : 0 < 3 * (m ^ 2 * σ ^ 4) := by positivity
      have h1 : (m * σ ^ 2) ^ 3 ≤ A ^ 2 * (3 * (m * σ ^ 2) ^ 2) :=
        h2.trans (mul_le_mul_of_nonneg_left h4 (sq_nonneg A))
      refine le_of_mul_le_mul_left ?_ hc
      linarith
  calc σ * Real.sqrt (m / 3) = Real.sqrt (σ ^ 2 * (m / 3)) := by
        rw [Real.sqrt_mul (sq_nonneg σ), Real.sqrt_sq hσ.le]
    _ ≤ Real.sqrt (A ^ 2) := Real.sqrt_le_sqrt hkey
    _ = A := Real.sqrt_sq hA

/-! ### Fact 2.2 -/

/-- **Fact 2.2 (sums of symmetric variables).** Let `X_i`, `i ∈ ι` (a finite index set with
`m` elements), be independent symmetric real random variables on a probability space, with
`E X_i² = σ²` and `E X_i⁴ ≤ 3σ⁴` (in particular the fourth moments are finite), where
`σ > 0`. Then `E|θ + Σ_i X_i| ≥ σ √(m/3)` for every real `θ`. -/
theorem fact_2_2_general {Ω ι : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] [Fintype ι] (X : ι → Ω → ℝ)
    (hindep : iIndepFun X μ)
    (hsymm : ∀ i, IdentDistrib (X i) (fun ω => -X i ω) μ μ)
    {σ : ℝ} (hσ : 0 < σ)
    (h2 : ∀ i, ∫ ω, X i ω ^ 2 ∂μ = σ ^ 2)
    (h4i : ∀ i, Integrable (fun ω => X i ω ^ 4) μ)
    (h4 : ∀ i, ∫ ω, X i ω ^ 4 ∂μ ≤ 3 * σ ^ 4)
    (θ : ℝ) :
    σ * Real.sqrt (Fintype.card ι / 3) ≤ ∫ ω, |θ + ∑ i, X i ω| ∂μ := by
  have hS : AEMeasurable (fun ω => ∑ i, X i ω) μ :=
    Finset.aemeasurable_fun_sum _ fun i _ => (hsymm i).aemeasurable_fst
  -- two moments: `X = Σ_i X_i` has `E X² = mσ²` and `E X⁴ ≤ 3m²σ⁴`; in particular `E|X| < ∞`
  obtain ⟨hS4, hm2, -⟩ := sum_moments X hindep hsymm h2 h4i Finset.univ
  have hm4 := sum_fourth_moment_le X hindep hsymm h2 h4i h4 Finset.univ
  rw [Finset.card_univ] at hm2 hm4
  have hS1 : Integrable (fun ω => ∑ i, X i ω) μ := by
    simpa only [pow_one] using
      integrable_pow_of_integrable_pow_four hS hS4 (k := 1) (by norm_num)
  -- the shift does not hurt: `E|θ + X| ≥ E|X|`
  have hshift : ∫ ω, |∑ i, X i ω| ∂μ ≤ ∫ ω, |θ + ∑ i, X i ω| ∂μ :=
    integral_abs_le_integral_abs_add_of_symm (identDistrib_sum_neg X hindep hsymm) hS1 θ
  -- from moments to the absolute value: `(E X²)³ ≤ (E|X|)² E X⁴`, so `E|X| ≥ σ √(m/3)`
  have hH := integral_sq_pow_three_le hS hS4
  rw [hm2] at hH
  exact (mul_sqrt_le_of_moments (Nat.cast_nonneg _) hσ (integral_nonneg fun ω => abs_nonneg _)
    hH hm4).trans hshift

end

end R56Audit
end

section
open MeasureTheory ProbabilityTheory

namespace TusnadyPlane.RandomPoints

theorem chk_fact_2_2 {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (m : ℕ) (X : Fin m → Ω → ℝ)
    (hX : ∀ i, Measurable (X i)) (hind : iIndepFun X μ)
    (hsym : ∀ i, Measure.map (X i) μ = Measure.map (fun ω => -X i ω) μ)
    (σ : ℝ) (hσ : 0 < σ)
    (hint2 : ∀ i, Integrable (fun ω => (X i ω)^2) μ)
    (hint4 : ∀ i, Integrable (fun ω => (X i ω)^4) μ)
    (hsecond : ∀ i, (∫ ω, (X i ω)^2 ∂μ) = σ^2)
    (hfourth : ∀ i, (∫ ω, (X i ω)^4 ∂μ) ≤ 3*σ^4) (θ : ℝ) :
    σ * Real.sqrt ((m : ℝ)/3) ≤ ∫ ω, |θ + ∑ i : Fin m, X i ω| ∂μ := by
  have h := R56Audit.fact_2_2_general X hind
    (fun i => ⟨(hX i).aemeasurable, (hX i).neg.aemeasurable, hsym i⟩) hσ hsecond hint4 hfourth θ
  simpa using h

end TusnadyPlane.RandomPoints
end

theorem solution : type_of% @TusnadyPlane.RandomPoints.chk_fact_2_2 := @TusnadyPlane.RandomPoints.chk_fact_2_2
