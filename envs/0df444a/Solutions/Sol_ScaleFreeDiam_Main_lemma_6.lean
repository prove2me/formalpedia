-- Prove2me | solution 1 for ScaleFreeDiam.Main.lemma_6
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-10-28T06:27:51.66479+00:00
-- url     : https://prove2.me/submissions/def99f07-c9b2-48f6-803f-848fb02dfce7

import Mathlib

namespace Prove2SwarmSubmission

/-! Full native revision after actual helper diagnostics. Graph and mean packet
bodies retain their checked declarations. Repaired scalar and final assembly
still require full independent compilation and kernel replay. -/

namespace ScaleFreeDiam.Main
namespace GraphScoutMGF

open MeasureTheory ProbabilityTheory

/-- `p i` is a probability. -/
theorem p_mem_Icc {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {k : ℕ} {X : Fin k → Ω → ℝ} {p : Fin k → ℝ} (hp : ∀ i, P.real {ω | X i ω = 1} = p i)
    (i : Fin k) : 0 ≤ p i ∧ p i ≤ 1 := by
  rw [← hp i]
  exact ⟨measureReal_nonneg, measureReal_le_one⟩

/-- Exact Bernoulli MGF: for a measurable, almost surely `{0,1}`-valued `Y`,
`E[exp (s Y)] = 1 + (exp s - 1) · P.real {Y = 1}`. -/
theorem mgf_eq_of_ae_zero_or_one {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {Y : Ω → ℝ} (hYm : Measurable Y)
    (hY : ∀ᵐ ω ∂P, Y ω = 0 ∨ Y ω = 1) (s : ℝ) :
    mgf Y P s = 1 + (Real.exp s - 1) * P.real {ω | Y ω = 1} := by
  have hE : MeasurableSet {ω | Y ω = 1} := hYm (measurableSet_singleton 1)
  have hae : (fun ω => Real.exp (s * Y ω)) =ᵐ[P]
      fun ω => 1 + (Real.exp s - 1) * {ω | Y ω = 1}.indicator 1 ω := by
    filter_upwards [hY] with ω hω
    rcases hω with h | h
    · have hn : ω ∉ {ω | Y ω = 1} := by
        rw [Set.mem_ofPred_eq, h]
        norm_num
      rw [Set.indicator_of_notMem hn, h]
      simp
    · have hm : ω ∈ {ω | Y ω = 1} := h
      rw [Set.indicator_of_mem hm, h]
      simp
  have hint : Integrable (fun ω => (Real.exp s - 1) * {ω | Y ω = 1}.indicator 1 ω) P :=
    ((integrable_const (1 : ℝ)).indicator hE).const_mul _
  rw [mgf, integral_congr_ae hae, integral_add (integrable_const _) hint, integral_const,
    integral_const_mul, integral_indicator_one hE, probReal_univ, smul_eq_mul, one_mul]

/-- Bernoulli MGF envelope `1 + (e^s - 1) q ≤ exp (q (e^s - 1))`, valid for every real `s`. -/
theorem mgf_le_exp_of_ae_zero_or_one {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {Y : Ω → ℝ} (hYm : Measurable Y)
    (hY : ∀ᵐ ω ∂P, Y ω = 0 ∨ Y ω = 1) (s : ℝ) :
    mgf Y P s ≤ Real.exp (P.real {ω | Y ω = 1} * (Real.exp s - 1)) := by
  rw [mgf_eq_of_ae_zero_or_one P hYm hY s]
  have h := Real.add_one_le_exp (P.real {ω | Y ω = 1} * (Real.exp s - 1))
  linarith

/-- Independent product: the MGF of the sum is the product of the Bernoulli MGFs. -/
theorem mgf_sum_eq_prod {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {k : ℕ} {X : Fin k → Ω → ℝ} (hXm : ∀ i, Measurable (X i))
    (hind : iIndepFun X P) (hX : ∀ i, ∀ᵐ ω ∂P, X i ω = 0 ∨ X i ω = 1)
    {p : Fin k → ℝ} (hp : ∀ i, P.real {ω | X i ω = 1} = p i) (s : ℝ) :
    mgf (fun ω => ∑ i, X i ω) P s = ∏ i, (1 + (Real.exp s - 1) * p i) := by
  have hfun : (fun ω => ∑ i, X i ω) = ∑ i, X i := by
    funext ω
    rw [Finset.sum_apply]
  rw [hfun, hind.mgf_sum hXm Finset.univ]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [mgf_eq_of_ae_zero_or_one P (hXm i) (hX i) s, hp i]

/-- MGF envelope of the sum: `E[exp (s ∑ X_i)] ≤ exp ((∑ p_i) (e^s - 1))` for every real `s`. -/
theorem mgf_sum_le_exp {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {k : ℕ} {X : Fin k → Ω → ℝ} (hXm : ∀ i, Measurable (X i))
    (hind : iIndepFun X P) (hX : ∀ i, ∀ᵐ ω ∂P, X i ω = 0 ∨ X i ω = 1)
    {p : Fin k → ℝ} (hp : ∀ i, P.real {ω | X i ω = 1} = p i) (s : ℝ) :
    mgf (fun ω => ∑ i, X i ω) P s ≤ Real.exp ((∑ i, p i) * (Real.exp s - 1)) := by
  rw [mgf_sum_eq_prod P hXm hind hX hp s, Finset.sum_mul, Real.exp_sum]
  refine Finset.prod_le_prod (fun i _ => ?_) (fun i _ => ?_)
  · rw [← hp i, ← mgf_eq_of_ae_zero_or_one P (hXm i) (hX i) s]
    exact mgf_nonneg
  · have h := Real.add_one_le_exp (p i * (Real.exp s - 1))
    linarith

/-- Exponential integrability of `s · ∑ X_i`, for every real `s`. -/
theorem integrable_exp_mul_sum {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {k : ℕ} {X : Fin k → Ω → ℝ} (hXm : ∀ i, Measurable (X i))
    (hind : iIndepFun X P) (hX : ∀ i, ∀ᵐ ω ∂P, X i ω = 0 ∨ X i ω = 1) (s : ℝ) :
    Integrable (fun ω => Real.exp (s * ∑ i, X i ω)) P := by
  have h01 : ∀ i, ∀ᵐ ω ∂P, X i ω ∈ Set.Icc (0 : ℝ) 1 := by
    intro i
    filter_upwards [hX i] with ω h
    rcases h with h | h <;> simp [h]
  have h := hind.integrable_exp_mul_sum (t := s) hXm (s := Finset.univ)
    (fun i _ => integrable_exp_mul_of_mem_Icc (hXm i).aemeasurable (h01 i))
  simpa [Finset.sum_apply] using h

/-- Chernoff upper-tail bridge in `P.real`, for any threshold `a` and any `s ≥ 0`. -/
theorem upper_tail_le {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {k : ℕ} {X : Fin k → Ω → ℝ} (hXm : ∀ i, Measurable (X i))
    (hind : iIndepFun X P) (hX : ∀ i, ∀ᵐ ω ∂P, X i ω = 0 ∨ X i ω = 1)
    {p : Fin k → ℝ} (hp : ∀ i, P.real {ω | X i ω = 1} = p i) (s : ℝ) (hs : 0 ≤ s) (a : ℝ) :
    P.real {ω | a ≤ ∑ i, X i ω} ≤
      Real.exp (-s * a) * Real.exp ((∑ i, p i) * (Real.exp s - 1)) := by
  calc P.real {ω | a ≤ ∑ i, X i ω}
      ≤ Real.exp (-s * a) * mgf (fun ω => ∑ i, X i ω) P s :=
        measure_ge_le_exp_mul_mgf a hs (integrable_exp_mul_sum P hXm hind hX s)
    _ ≤ Real.exp (-s * a) * Real.exp ((∑ i, p i) * (Real.exp s - 1)) :=
        mul_le_mul_of_nonneg_left (mgf_sum_le_exp P hXm hind hX hp s) (Real.exp_pos _).le

/-- Chernoff lower-tail bridge in `P.real`, for any threshold `a` and any `s ≥ 0`
(the MGF is evaluated at `-s`). -/
theorem lower_tail_le {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {k : ℕ} {X : Fin k → Ω → ℝ} (hXm : ∀ i, Measurable (X i))
    (hind : iIndepFun X P) (hX : ∀ i, ∀ᵐ ω ∂P, X i ω = 0 ∨ X i ω = 1)
    {p : Fin k → ℝ} (hp : ∀ i, P.real {ω | X i ω = 1} = p i) (s : ℝ) (hs : 0 ≤ s) (a : ℝ) :
    P.real {ω | ∑ i, X i ω ≤ a} ≤
      Real.exp (s * a) * Real.exp ((∑ i, p i) * (Real.exp (-s) - 1)) := by
  have h : P.real {ω | ∑ i, X i ω ≤ a} ≤
      Real.exp (-(-s) * a) * mgf (fun ω => ∑ i, X i ω) P (-s) :=
    measure_le_le_exp_mul_mgf a (neg_nonpos.mpr hs) (integrable_exp_mul_sum P hXm hind hX (-s))
  rw [neg_neg] at h
  calc P.real {ω | ∑ i, X i ω ≤ a}
      ≤ Real.exp (s * a) * mgf (fun ω => ∑ i, X i ω) P (-s) := h
    _ ≤ Real.exp (s * a) * Real.exp ((∑ i, p i) * (Real.exp (-s) - 1)) :=
        mul_le_mul_of_nonneg_left (mgf_sum_le_exp P hXm hind hX hp (-s)) (Real.exp_pos _).le

/-- The frozen upper-tail event of `lemma_6`, as one exponential:
`P.real {μ + t ≤ ∑ X_i} ≤ exp (μ (e^s - 1) - s (μ + t))` for `s ≥ 0`. -/
theorem upper_event_le {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {k : ℕ} {X : Fin k → Ω → ℝ} (hXm : ∀ i, Measurable (X i))
    (hind : iIndepFun X P) (hX : ∀ i, ∀ᵐ ω ∂P, X i ω = 0 ∨ X i ω = 1)
    {p : Fin k → ℝ} (hp : ∀ i, P.real {ω | X i ω = 1} = p i) (t s : ℝ) (hs : 0 ≤ s) :
    P.real {ω | (∑ i, p i) + t ≤ ∑ i, X i ω} ≤
      Real.exp ((∑ i, p i) * (Real.exp s - 1) - s * ((∑ i, p i) + t)) := by
  have h := upper_tail_le P hXm hind hX hp s hs ((∑ i, p i) + t)
  rw [← Real.exp_add] at h
  calc P.real {ω | (∑ i, p i) + t ≤ ∑ i, X i ω}
      ≤ Real.exp (-s * ((∑ i, p i) + t) + (∑ i, p i) * (Real.exp s - 1)) := h
    _ = Real.exp ((∑ i, p i) * (Real.exp s - 1) - s * ((∑ i, p i) + t)) := by
        congr 1
        ring

/-- The frozen lower-tail event of `lemma_6`, as one exponential:
`P.real {∑ X_i ≤ μ - t} ≤ exp (μ (e^(-s) - 1) + s (μ - t))` for `s ≥ 0`. -/
theorem lower_event_le {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {k : ℕ} {X : Fin k → Ω → ℝ} (hXm : ∀ i, Measurable (X i))
    (hind : iIndepFun X P) (hX : ∀ i, ∀ᵐ ω ∂P, X i ω = 0 ∨ X i ω = 1)
    {p : Fin k → ℝ} (hp : ∀ i, P.real {ω | X i ω = 1} = p i) (t s : ℝ) (hs : 0 ≤ s) :
    P.real {ω | ∑ i, X i ω ≤ (∑ i, p i) - t} ≤
      Real.exp ((∑ i, p i) * (Real.exp (-s) - 1) + s * ((∑ i, p i) - t)) := by
  have h := lower_tail_le P hXm hind hX hp s hs ((∑ i, p i) - t)
  rw [← Real.exp_add] at h
  calc P.real {ω | ∑ i, X i ω ≤ (∑ i, p i) - t}
      ≤ Real.exp (s * ((∑ i, p i) - t) + (∑ i, p i) * (Real.exp (-s) - 1)) := h
    _ = Real.exp ((∑ i, p i) * (Real.exp (-s) - 1) + s * ((∑ i, p i) - t)) := by
        congr 1
        ring

/-- Trivial probability bound, for the degenerate cases (`μ = 0`, `t = 0`, ...). -/
theorem measureReal_le_one' {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (S : Set Ω) : P.real S ≤ 1 :=
  measureReal_le_one

end GraphScoutMGF
end ScaleFreeDiam.Main

namespace ScaleFreeDiam.NativeBridge

open MeasureTheory ProbabilityTheory

variable {Ω : Type*} [MeasurableSpace Ω]

theorem bernoulli_ae_eq_indicator (P : Measure Ω) {k : ℕ} (X : Fin k → Ω → ℝ)
    (hX : ∀ i, ∀ᵐ ω ∂P, X i ω = 0 ∨ X i ω = 1) (i : Fin k) :
    X i =ᵐ[P] {ω | X i ω = 1}.indicator (fun _ => (1 : ℝ)) := by
  filter_upwards [hX i] with ω hω
  rcases hω with h | h <;> simp [h]

theorem bernoulli_integrable (P : Measure Ω) [IsProbabilityMeasure P] {k : ℕ}
    (X : Fin k → Ω → ℝ) (hXm : ∀ i, Measurable (X i))
    (hX : ∀ i, ∀ᵐ ω ∂P, X i ω = 0 ∨ X i ω = 1) (i : Fin k) :
    Integrable (X i) P := by
  have hs : MeasurableSet {ω | X i ω = 1} := hXm i (measurableSet_singleton 1)
  exact ((integrable_const (1 : ℝ)).indicator hs).congr
    (bernoulli_ae_eq_indicator P X hX i).symm

theorem bernoulli_integral_eq (P : Measure Ω) [IsProbabilityMeasure P] {k : ℕ}
    (X : Fin k → Ω → ℝ) (hXm : ∀ i, Measurable (X i))
    (hX : ∀ i, ∀ᵐ ω ∂P, X i ω = 0 ∨ X i ω = 1) (p : Fin k → ℝ)
    (hp : ∀ i, P.real {ω | X i ω = 1} = p i) (i : Fin k) :
    ∫ ω, X i ω ∂P = p i := by
  have hs : MeasurableSet {ω | X i ω = 1} := hXm i (measurableSet_singleton 1)
  rw [integral_congr_ae (bernoulli_ae_eq_indicator P X hX i),
    integral_indicator_const _ hs, smul_eq_mul, mul_one]
  exact hp i

theorem integral_sum_eq (P : Measure Ω) [IsProbabilityMeasure P] {k : ℕ}
    (X : Fin k → Ω → ℝ) (hXm : ∀ i, Measurable (X i))
    (hX : ∀ i, ∀ᵐ ω ∂P, X i ω = 0 ∨ X i ω = 1) (p : Fin k → ℝ)
    (hp : ∀ i, P.real {ω | X i ω = 1} = p i) :
    ∫ ω, ∑ i, X i ω ∂P = ∑ i, p i := by
  rw [integral_finsetSum Finset.univ (fun i _ => bernoulli_integrable P X hXm hX i)]
  exact Finset.sum_congr rfl (fun i _ => bernoulli_integral_eq P X hXm hX p hp i)

theorem bernoulli_param_nonneg (P : Measure Ω) {k : ℕ} (X : Fin k → Ω → ℝ)
    (p : Fin k → ℝ) (hp : ∀ i, P.real {ω | X i ω = 1} = p i) (i : Fin k) :
    0 ≤ p i := by
  rw [← hp i]
  exact ENNReal.toReal_nonneg

theorem ae_eq_zero_of_param_eq_zero (P : Measure Ω) [IsProbabilityMeasure P] {k : ℕ}
    (X : Fin k → Ω → ℝ) (hX : ∀ i, ∀ᵐ ω ∂P, X i ω = 0 ∨ X i ω = 1) (p : Fin k → ℝ)
    (hp : ∀ i, P.real {ω | X i ω = 1} = p i) (i : Fin k) (hpi : p i = 0) :
    ∀ᵐ ω ∂P, X i ω = 0 := by
  have hreal : (P {ω | X i ω = 1}).toReal = 0 := (hp i).trans hpi
  have hzero : P {ω | X i ω = 1} = 0 := by
    rcases (ENNReal.toReal_eq_zero_iff _).mp hreal with h | h
    · exact h
    · exact absurd h (measure_ne_top P _)
  have hne : ∀ᵐ ω ∂P, X i ω ≠ 1 := by
    rw [ae_iff]
    refine measure_mono_null ?_ hzero
    intro ω hω
    by_contra hω1
    exact hω hω1
  filter_upwards [hX i, hne] with ω h01 h1
  exact h01.resolve_right h1

theorem sum_ae_eq_zero_of_sum_param_eq_zero (P : Measure Ω) [IsProbabilityMeasure P]
    {k : ℕ} (X : Fin k → Ω → ℝ) (hX : ∀ i, ∀ᵐ ω ∂P, X i ω = 0 ∨ X i ω = 1)
    (p : Fin k → ℝ) (hp : ∀ i, P.real {ω | X i ω = 1} = p i) (hμ : ∑ i, p i = 0) :
    ∀ᵐ ω ∂P, ∑ i, X i ω = 0 := by
  have hpi : ∀ i, p i = 0 := fun i =>
    (Finset.sum_eq_zero_iff_of_nonneg
      (fun j _ => bernoulli_param_nonneg P X p hp j)).mp hμ i (Finset.mem_univ i)
  have hall : ∀ᵐ ω ∂P, ∀ i, X i ω = 0 :=
    ae_all_iff.mpr (fun i => ae_eq_zero_of_param_eq_zero P X hX p hp i (hpi i))
  filter_upwards [hall] with ω hω
  exact Finset.sum_eq_zero (fun i _ => hω i)

theorem upper_event_real_eq_zero_of_mean_zero (P : Measure Ω) [IsProbabilityMeasure P]
    {k : ℕ} (X : Fin k → Ω → ℝ) (hX : ∀ i, ∀ᵐ ω ∂P, X i ω = 0 ∨ X i ω = 1)
    (p : Fin k → ℝ) (hp : ∀ i, P.real {ω | X i ω = 1} = p i) (hμ : ∑ i, p i = 0)
    {t : ℝ} (ht : 0 < t) :
    P.real {ω | (∑ i, p i) + t ≤ ∑ i, X i ω} = 0 := by
  have hS := sum_ae_eq_zero_of_sum_param_eq_zero P X hX p hp hμ
  have hnull : P {ω | (∑ i, p i) + t ≤ ∑ i, X i ω} = 0 := by
    refine measure_mono_null ?_ (ae_iff.mp hS)
    intro ω hω hS0
    change (∑ i, p i) + t ≤ ∑ i, X i ω at hω
    change ∑ i, X i ω = 0 at hS0
    linarith
  show (P {ω | (∑ i, p i) + t ≤ ∑ i, X i ω}).toReal = 0
  rw [hnull]
  simp

end ScaleFreeDiam.NativeBridge

namespace NativeScaleFreeUpper

open Set

theorem log_factor_nonneg (x : ℝ) (hx : 0 ≤ x) :
    0 ≤ (2 + x) * Real.log (1 + x) - 2 * x := by
  have hden : 0 < x + 2 := by linarith
  have hlog : 2 * x ≤ Real.log (1 + x) * (x + 2) :=
    (div_le_iff₀ hden).mp (Real.le_log_one_add_of_nonneg hx)
  nlinarith


theorem bennett_upper (x : ℝ) (hx : 0 ≤ x) :
    x ^ 2 / (2 * (1 + x / 3)) ≤
      (1 + x) * Real.log (1 + x) - x := by
  let F : ℝ → ℝ := fun y =>
    (2 + (2 / 3 : ℝ) * y) * ((1 + y) * Real.log (1 + y) - y) - y ^ 2
  have hderiv : ∀ y : ℝ, 0 ≤ y →
      HasDerivAt F ((4 / 3 : ℝ) * ((2 + y) * Real.log (1 + y) - 2 * y)) y := by
    intro y hy
    have hpos : 0 < 1 + y := by linarith
    have hid : HasDerivAt (fun z : ℝ => z) 1 y := hasDerivAt_id y
    have hlin : HasDerivAt (fun z : ℝ => 1 + z) 1 y := hid.const_add 1
    have hlog : HasDerivAt (fun z : ℝ => Real.log (1 + z)) (1 / (1 + y)) y :=
      hlin.log hpos.ne'
    have hentropy : HasDerivAt
        (fun z : ℝ => (1 + z) * Real.log (1 + z) - z)
        (Real.log (1 + y)) y := by
      apply ((hlin.mul hlog).sub hid).congr_deriv
      field_simp [hpos.ne']
      ring
    have hfac : HasDerivAt (fun z : ℝ => 2 + (2 / 3 : ℝ) * z)
        (2 / 3 : ℝ) y := by
      simpa using (hid.const_mul (2 / 3 : ℝ)).const_add 2
    apply ((hfac.mul hentropy).sub (hasDerivAt_pow 2 y)).congr_deriv
    norm_num
    ring
  have hderiv_nonneg : ∀ y : ℝ, 0 ≤ y →
      0 ≤ (4 / 3 : ℝ) * ((2 + y) * Real.log (1 + y) - 2 * y) := by
    intro y hy
    exact mul_nonneg (by norm_num) (log_factor_nonneg y hy)
  have hmono : MonotoneOn F (Ici (0 : ℝ)) :=
    monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici (0 : ℝ))
      (fun y hy => (hderiv y hy).continuousAt.continuousWithinAt)
      (fun y hy => (hderiv y (interior_subset hy)).hasDerivWithinAt)
      (fun y hy => hderiv_nonneg y (interior_subset hy))
  have hFx : 0 ≤ F x := by
    have h := hmono (show (0 : ℝ) ∈ Ici (0 : ℝ) by simp) hx hx
    simpa [F] using h
  have hden : 0 < 2 * (1 + x / 3) := by positivity
  apply (div_le_iff₀ hden).2
  dsimp only [F] at hFx
  nlinarith [hFx]

end NativeScaleFreeUpper

namespace NativeScaleFreeUpperOptimization

open Set

theorem scaled_bennett_upper (μ t : ℝ) (hμ : 0 < μ) (ht : 0 ≤ t) :
    t ^ 2 / (2 * (μ + t / 3)) ≤
      (μ + t) * Real.log (1 + t / μ) - t := by
  let x : ℝ := t / μ
  have hx : 0 ≤ x := div_nonneg ht hμ.le
  have hμx : μ * x = t := by
    dsimp only [x]
    field_simp [hμ.ne']
  have hdenx : 0 < 2 * (1 + x / 3) := by positivity
  have hbound : x ^ 2 ≤
      ((1 + x) * Real.log (1 + x) - x) * (2 * (1 + x / 3)) :=
    (div_le_iff₀ hdenx).mp (NativeScaleFreeUpper.bennett_upper x hx)
  have hxx : μ ^ 2 * x ^ 2 = t ^ 2 := by
    calc
      μ ^ 2 * x ^ 2 = (μ * x) ^ 2 := by ring
      _ = t ^ 2 := by rw [hμx]
  have hH : μ * ((1 + x) * Real.log (1 + x) - x) =
      (μ + t) * Real.log (1 + x) - t := by
    calc
      _ = (μ + μ * x) * Real.log (1 + x) - μ * x := by ring
      _ = _ := by rw [hμx]
  have hB : μ * (2 * (1 + x / 3)) = 2 * (μ + t / 3) := by
    calc
      _ = 2 * (μ + μ * x / 3) := by ring
      _ = _ := by rw [hμx]
  have hden : 0 < 2 * (μ + t / 3) := by positivity
  apply (div_le_iff₀ hden).2
  change t ^ 2 ≤ ((μ + t) * Real.log (1 + x) - t) * (2 * (μ + t / 3))
  calc
    t ^ 2 = μ ^ 2 * x ^ 2 := hxx.symm
    _ ≤ μ ^ 2 * (((1 + x) * Real.log (1 + x) - x) * (2 * (1 + x / 3))) :=
      mul_le_mul_of_nonneg_left hbound (sq_nonneg μ)
    _ = (μ * ((1 + x) * Real.log (1 + x) - x)) *
          (μ * (2 * (1 + x / 3))) := by ring
    _ = ((μ + t) * Real.log (1 + x) - t) * (2 * (μ + t / 3)) := by
      rw [hH, hB]


theorem upper_optimizer_nonneg (μ t : ℝ) (hμ : 0 < μ) (ht : 0 ≤ t) :
    0 ≤ Real.log (1 + t / μ) := by
  apply Real.log_nonneg
  linarith [div_nonneg ht hμ.le]


theorem upper_optimizer_exp (μ t : ℝ) (hμ : 0 < μ) (ht : 0 ≤ t) :
    Real.exp (Real.log (1 + t / μ)) = 1 + t / μ := by
  apply Real.exp_log
  positivity


theorem upper_optimized_exponent (μ t : ℝ) (hμ : 0 < μ) (ht : 0 ≤ t) :
    μ * (Real.exp (Real.log (1 + t / μ)) - 1) -
        Real.log (1 + t / μ) * (μ + t) ≤
      -(t ^ 2 / (2 * (μ + t / 3))) := by
  have hdiv : μ * (t / μ) = t := by
    field_simp [hμ.ne']
  have h := scaled_bennett_upper μ t hμ ht
  rw [upper_optimizer_exp μ t hμ ht]
  nlinarith


theorem upper_optimizer (μ t : ℝ) (hμ : 0 < μ) (ht : 0 ≤ t) :
    let s := Real.log (1 + t / μ)
    0 ≤ s ∧ μ * (Real.exp s - 1) - s * (μ + t) ≤
      -(t ^ 2 / (2 * (μ + t / 3))) := by
  dsimp only
  exact ⟨upper_optimizer_nonneg μ t hμ ht, upper_optimized_exponent μ t hμ ht⟩

end NativeScaleFreeUpperOptimization

namespace NativeScaleFreeLower

open Set

theorem exp_neg_le_quadratic (s : ℝ) (hs : 0 ≤ s) :
    Real.exp (-s) ≤ 1 - s + s ^ 2 / 2 := by
  have hf (x : ℝ) :
      HasDerivAt (fun y : ℝ => Real.exp (-y)) (-Real.exp (-x)) x := by
    apply ((Real.hasDerivAt_exp (-x)).comp x ((hasDerivAt_id x).neg)).congr_deriv
    ring
  have hg (x : ℝ) :
      HasDerivAt (fun y : ℝ => 1 - y + y ^ 2 / 2) (x - 1) x := by
    apply (((hasDerivAt_const x (1 : ℝ)).sub (hasDerivAt_id x)).add
      (((hasDerivAt_id x).pow 2).div_const (2 : ℝ))).congr_deriv
    simp only [id_eq]
    ring
  have hbound (x : ℝ) : -Real.exp (-x) ≤ x - 1 := by
    have hexp := Real.add_one_le_exp (-x)
    linarith
  exact image_le_of_deriv_right_le_deriv_boundary
    (a := 0) (b := s)
    (f := fun x : ℝ => Real.exp (-x))
    (f' := fun x : ℝ => -Real.exp (-x))
    (B := fun x : ℝ => 1 - x + x ^ 2 / 2)
    (B' := fun x : ℝ => x - 1)
    (fun x _ => (hf x).continuousAt.continuousWithinAt)
    (fun x _ => (hf x).hasDerivWithinAt)
    (by simp)
    (fun x _ => (hg x).continuousAt.continuousWithinAt)
    (fun x _ => (hg x).hasDerivWithinAt)
    (fun x _ => hbound x)
    (show s ∈ Icc 0 s from ⟨hs, le_rfl⟩)


theorem lower_exponent_le_quadratic
    (mu t s : ℝ) (hmu : 0 ≤ mu) (hs : 0 ≤ s) :
    mu * (Real.exp (-s) - 1) + s * (mu - t) ≤
      mu * s ^ 2 / 2 - s * t := by
  have h := mul_le_mul_of_nonneg_left (exp_neg_le_quadratic s hs) hmu
  nlinarith only [h]


theorem quadratic_lower_optimizer
    (mu t : ℝ) (hmu : 0 < mu) :
    mu * (t / mu) ^ 2 / 2 - (t / mu) * t =
      -(t ^ 2 / (2 * mu)) := by
  have hmul : mu * (t / mu) = t :=
    (mul_comm mu (t / mu)).trans (div_mul_cancel₀ t hmu.ne')
  have hsq : mu * (t / mu) ^ 2 = (t / mu) * t := by
    rw [pow_two, ← mul_assoc, hmul]
    exact mul_comm t (t / mu)
  rw [hsq]
  simp only [div_eq_mul_inv, mul_inv]
  ring


theorem lower_chernoff_exponent_at_ratio
    (mu t : ℝ) (hmu : 0 < mu) (ht : 0 ≤ t) :
    mu * (Real.exp (-(t / mu)) - 1) + (t / mu) * (mu - t) ≤
      -(t ^ 2 / (2 * mu)) := by
  calc
    mu * (Real.exp (-(t / mu)) - 1) + (t / mu) * (mu - t) ≤
        mu * (t / mu) ^ 2 / 2 - (t / mu) * t :=
      lower_exponent_le_quadratic mu t (t / mu) hmu.le
        (div_nonneg ht hmu.le)
    _ = -(t ^ 2 / (2 * mu)) := quadratic_lower_optimizer mu t hmu

end NativeScaleFreeLower

namespace ScaleFreeDiam.NativeVerifiedEndpoints

open MeasureTheory ProbabilityTheory

/-- Exact zero-mean target tails. The checked NativeBridge above supplies the positive
upper-event nullity; no faulty artifact probability endpoint declarations are reused. -/
theorem zero_mean_bounds
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (k : ℕ) (X : Fin k → Ω → ℝ)
    (hX : ∀ i, ∀ᵐ ω ∂P, X i ω = 0 ∨ X i ω = 1)
    (p : Fin k → ℝ) (hp : ∀ i, P.real {ω | X i ω = 1} = p i)
    (hμ : ∑ i, p i = 0) (t : ℝ) (ht : 0 ≤ t) :
    P.real {ω | (∑ i, p i) + t ≤ ∑ i, X i ω} ≤
      Real.exp (-(t ^ 2 / (2 * ((∑ i, p i) + t / 3)))) ∧
    P.real {ω | ∑ i, X i ω ≤ (∑ i, p i) - t} ≤
      Real.exp (-(t ^ 2 / (2 * (∑ i, p i)))) := by
  by_cases ht0 : t = 0
  · subst t
    constructor <;> simp
  · have htpos : 0 < t := lt_of_le_of_ne ht (Ne.symm ht0)
    constructor
    · have hnull :=
        ScaleFreeDiam.NativeBridge.upper_event_real_eq_zero_of_mean_zero
          P X hX p hp hμ (t := t) htpos
      rw [hnull]
      exact (Real.exp_pos _).le
    · simp only [hμ, mul_zero, div_zero, neg_zero, Real.exp_zero]
      exact measureReal_le_one

end ScaleFreeDiam.NativeVerifiedEndpoints

namespace ScaleFreeDiam.Main

open Filter Topology MeasureTheory ProbabilityTheory
open scoped Classical

theorem lemma_6 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (k : ℕ) (X : Fin k → Ω → ℝ) (hXm : ∀ i, Measurable (X i)) (hind : iIndepFun X P)
    (hX : ∀ i, ∀ᵐ ω ∂P, X i ω = 0 ∨ X i ω = 1)
    (p : Fin k → ℝ) (hp : ∀ i, P.real {ω | X i ω = 1} = p i) (t : ℝ) (ht : 0 ≤ t) :
    P.real {ω | (∑ i, p i) + t ≤ ∑ i, X i ω} ≤
        Real.exp (-(t ^ 2 / (2 * ((∑ i, p i) + t / 3)))) ∧
      P.real {ω | ∑ i, X i ω ≤ (∑ i, p i) - t} ≤
        Real.exp (-(t ^ 2 / (2 * (∑ i, p i)))) := by
  let mu : ℝ := ∑ i, p i
  have hmu0 : 0 ≤ mu :=
    Finset.sum_nonneg (fun i _ =>
      ScaleFreeDiam.NativeBridge.bernoulli_param_nonneg P X p hp i)
  by_cases hmu : mu = 0
  · exact ScaleFreeDiam.NativeVerifiedEndpoints.zero_mean_bounds
      P k X hX p hp hmu t ht
  · have hmupos : 0 < mu := lt_of_le_of_ne hmu0 (Ne.symm hmu)
    constructor
    · have hopt := NativeScaleFreeUpperOptimization.upper_optimizer mu t hmupos ht
      have htail := GraphScoutMGF.upper_event_le P hXm hind hX hp t
        (Real.log (1 + t / mu)) hopt.1
      exact htail.trans (Real.exp_le_exp.mpr hopt.2)
    · have htail := GraphScoutMGF.lower_event_le P hXm hind hX hp t
        (t / mu) (div_nonneg ht hmupos.le)
      exact htail.trans (Real.exp_le_exp.mpr
        (NativeScaleFreeLower.lower_chernoff_exponent_at_ratio mu t hmupos ht))

end ScaleFreeDiam.Main

end Prove2SwarmSubmission

open Filter Topology MeasureTheory ProbabilityTheory
open scoped Classical
theorem solution {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (k : ℕ) (X : Fin k → Ω → ℝ) (hXm : ∀ i, Measurable (X i)) (hind : iIndepFun X P)
    (hX : ∀ i, ∀ᵐ ω ∂P, X i ω = 0 ∨ X i ω = 1)
    (p : Fin k → ℝ) (hp : ∀ i, P.real {ω | X i ω = 1} = p i) (t : ℝ) (ht : 0 ≤ t) :
    P.real {ω | (∑ i, p i) + t ≤ ∑ i, X i ω} ≤
        Real.exp (-(t ^ 2 / (2 * ((∑ i, p i) + t / 3)))) ∧
      P.real {ω | ∑ i, X i ω ≤ (∑ i, p i) - t} ≤
        Real.exp (-(t ^ 2 / (2 * (∑ i, p i)))) := by
  exact Prove2SwarmSubmission.ScaleFreeDiam.Main.lemma_6 P k X hXm hind hX p hp t ht
