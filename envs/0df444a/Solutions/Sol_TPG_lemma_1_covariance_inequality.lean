-- Prove2me | solution 1 for TPG.lemma_1_covariance_inequality
-- status  : ACCEPTED   (prove)
-- author  : @Wenqian Xing
-- created : 2026-10-12T03:45:04.343125+00:00
-- url     : https://prove2.me/submissions/87e42e36-9e56-41cd-a68a-2355590939d1

import Mathlib

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

/-- One step of Doukhan's argument: for `X` measurable w.r.t. a sub-sigma-algebra `m` and bounded
by `a`, and `Y` integrable, `|E[XY] - E[X]E[Y]|` is controlled by `2a (∫_A Y - μ(A) E[Y])` for an
`m`-measurable set `A` (namely `A = {E[Y | m] - E[Y] ≥ 0}`). -/
theorem cov_step_aux {Ω : Type} {mΩ : MeasurableSpace Ω}
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (m : MeasurableSpace Ω) (hm : m ≤ mΩ)
    (X Y : Ω → ℝ) (hX : Measurable[m] X) (a : ℝ) (hXa : ∀ᵐ ω ∂μ, |X ω| ≤ a)
    (hY : Integrable Y μ) :
    ∃ A : Set Ω, MeasurableSet[m] A ∧
      |∫ ω, X ω * Y ω ∂μ - (∫ ω, X ω ∂μ) * ∫ ω, Y ω ∂μ|
        ≤ 2 * a * (∫ ω in A, Y ω ∂μ - μ.real A * ∫ ω, Y ω ∂μ) := by
  set c : ℝ := ∫ ω, Y ω ∂μ with hc
  set W : Ω → ℝ := μ[Y | m] with hW
  have hWm : StronglyMeasurable[m] W := stronglyMeasurable_condExp
  have hWint : Integrable W μ := integrable_condExp
  have hXsm : StronglyMeasurable[m] X := hX.stronglyMeasurable
  have hXae : AEStronglyMeasurable[mΩ] X μ := (hXsm.mono hm).aestronglyMeasurable
  have hXbd : ∀ᵐ ω ∂μ, ‖X ω‖ ≤ a := by simpa [Real.norm_eq_abs] using hXa
  have hXint : Integrable X μ :=
    (MemLp.of_bound hXae a hXbd (p := 1)).integrable le_rfl
  have hXW : Integrable (fun ω => X ω * W ω) μ := hWint.bdd_mul hXae hXbd
  have h1 : ∫ ω, X ω * Y ω ∂μ = ∫ ω, X ω * W ω ∂μ := by
    have hpull : μ[X * Y | m] =ᵐ[μ] X * W :=
      condExp_stronglyMeasurable_mul_of_bound hm hXsm hY a hXbd
    calc ∫ ω, X ω * Y ω ∂μ = ∫ ω, (μ[X * Y | m]) ω ∂μ := (integral_condExp hm).symm
      _ = ∫ ω, X ω * W ω ∂μ := integral_congr_ae hpull
  set Z : Ω → ℝ := fun ω => W ω - c with hZ
  have hZm : StronglyMeasurable[m] Z := hWm.sub stronglyMeasurable_const
  have hZint : Integrable Z μ := hWint.sub (integrable_const c)
  have hZ0 : ∫ ω, Z ω ∂μ = 0 := by
    have : ∫ ω, Z ω ∂μ = ∫ ω, W ω ∂μ - ∫ _ω, c ∂μ := integral_sub hWint (integrable_const c)
    rw [this, hW, integral_condExp hm]
    simp [hc]
  have h2 : ∫ ω, X ω * Y ω ∂μ - (∫ ω, X ω ∂μ) * c = ∫ ω, X ω * Z ω ∂μ := by
    rw [h1]
    have hfun : (fun ω => X ω * Z ω) = fun ω => X ω * W ω - X ω * c := by
      funext ω
      simp only [hZ]
      ring
    rw [hfun, integral_sub hXW (hXint.mul_const c), integral_mul_const]
  have hAm : MeasurableSet[m] {ω | 0 ≤ Z ω} :=
    (stronglyMeasurable_const : StronglyMeasurable[m] (fun _ : Ω => (0 : ℝ))).measurableSet_le hZm
  refine ⟨{ω | 0 ≤ Z ω}, hAm, ?_⟩
  set A : Set Ω := {ω | 0 ≤ Z ω} with hA
  have hAm' : MeasurableSet[mΩ] A := hm _ hAm
  have habsZ : ∫ ω, |Z ω| ∂μ = 2 * ∫ ω in A, Z ω ∂μ := by
    have hfun : (fun ω => |Z ω|) = fun ω => 2 * A.indicator Z ω - Z ω := by
      funext ω
      by_cases h : ω ∈ A
      · have h0 : 0 ≤ Z ω := h
        rw [Set.indicator_of_mem h, abs_of_nonneg h0]
        ring
      · have h0 : Z ω < 0 := not_le.mp h
        rw [Set.indicator_of_notMem h, abs_of_neg h0]
        ring
    rw [hfun, integral_sub ((hZint.indicator hAm').const_mul 2) hZint, integral_const_mul,
      integral_indicator hAm', hZ0, sub_zero]
  have hsetZ : ∫ ω in A, Z ω ∂μ = ∫ ω in A, Y ω ∂μ - μ.real A * c := by
    have : ∫ ω in A, Z ω ∂μ = ∫ ω in A, W ω ∂μ - ∫ _ω in A, c ∂μ :=
      integral_sub hWint.integrableOn (integrable_const c).integrableOn
    rw [this, hW, setIntegral_condExp hm hY hAm, setIntegral_const, smul_eq_mul]
  rw [h2]
  calc |∫ ω, X ω * Z ω ∂μ| ≤ ∫ ω, |X ω * Z ω| ∂μ := abs_integral_le_integral_abs
    _ ≤ ∫ ω, a * |Z ω| ∂μ := by
        apply integral_mono_ae
        · exact (hZint.bdd_mul hXae hXbd).abs
        · exact hZint.abs.const_mul a
        · filter_upwards [hXa] with ω hω
          rw [abs_mul]
          exact mul_le_mul_of_nonneg_right hω (abs_nonneg _)
    _ = a * ∫ ω, |Z ω| ∂μ := integral_const_mul _ _
    _ = 2 * a * (∫ ω in A, Y ω ∂μ - μ.real A * c) := by
        rw [habsZ, hsetZ]
        ring

theorem solution {Ω : Type} [mΩ : MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (mU mV : MeasurableSpace Ω) (hU : mU ≤ mΩ) (hV : mV ≤ mΩ)
    (X Y : Ω → ℝ) (hX : Measurable[mU] X) (hY : Measurable[mV] Y)
    (a b α : ℝ) (hXa : ∀ᵐ ω ∂μ, |X ω| ≤ a) (hYb : ∀ᵐ ω ∂μ, |Y ω| ≤ b)
    (hα : ∀ A B : Set Ω, MeasurableSet[mU] A → MeasurableSet[mV] B →
      |μ.real (A ∩ B) - μ.real A * μ.real B| ≤ α) :
    |cov[X, Y; μ]| ≤ 4 * α * a * b := by
  -- nonnegativity of the constants
  have ha0 : 0 ≤ a := by
    obtain ⟨ω, hω⟩ := hXa.exists
    exact (abs_nonneg _).trans hω
  have hb0 : 0 ≤ b := by
    obtain ⟨ω, hω⟩ := hYb.exists
    exact (abs_nonneg _).trans hω
  -- measurability / integrability
  have hXae : AEStronglyMeasurable[mΩ] X μ := (hX.mono hU le_rfl).aestronglyMeasurable
  have hYae : AEStronglyMeasurable[mΩ] Y μ := (hY.mono hV le_rfl).aestronglyMeasurable
  have hXbd : ∀ᵐ ω ∂μ, ‖X ω‖ ≤ a := by simpa [Real.norm_eq_abs] using hXa
  have hYbd : ∀ᵐ ω ∂μ, ‖Y ω‖ ≤ b := by simpa [Real.norm_eq_abs] using hYb
  have hX2 : MemLp X 2 μ := MemLp.of_bound hXae a hXbd
  have hY2 : MemLp Y 2 μ := MemLp.of_bound hYae b hYbd
  have hYint : Integrable Y μ := hY2.integrable (by norm_num)
  have hcov : cov[X, Y; μ] = ∫ ω, X ω * Y ω ∂μ - (∫ ω, X ω ∂μ) * ∫ ω, Y ω ∂μ := by
    rw [covariance_eq_sub hX2 hY2]
    rfl
  -- first step: condition on `mU`
  obtain ⟨A, hA, hstepA⟩ := cov_step_aux μ mU hU X Y hX a hXa hYint
  have hA' : MeasurableSet[mΩ] A := hU _ hA
  have hindA : Integrable (A.indicator (fun _ => (1 : ℝ))) μ :=
    (integrable_const (1 : ℝ)).indicator hA'
  -- second step: condition on `mV`
  obtain ⟨B, hB, hstepB⟩ :=
    cov_step_aux μ mV hV Y (A.indicator (fun _ => (1 : ℝ))) hY b hYb hindA
  have hB' : MeasurableSet[mΩ] B := hV _ hB
  have e1 : ∫ ω, Y ω * A.indicator (fun _ => (1 : ℝ)) ω ∂μ = ∫ ω in A, Y ω ∂μ := by
    rw [← integral_indicator hA']
    congr 1
    funext ω
    by_cases h : ω ∈ A
    · simp [Set.indicator_of_mem h]
    · simp [Set.indicator_of_notMem h]
  have e2 : ∫ ω, A.indicator (fun _ => (1 : ℝ)) ω ∂μ = μ.real A := by
    rw [integral_indicator hA', setIntegral_const, smul_eq_mul, mul_one]
  have e3 : ∫ ω in B, A.indicator (fun _ => (1 : ℝ)) ω ∂μ = μ.real (A ∩ B) := by
    rw [integral_indicator hA', Measure.restrict_restrict hA', setIntegral_const, smul_eq_mul,
      mul_one]
  rw [e1, e2, e3] at hstepB
  have hAB := hα A B hA hB
  have hAB' : μ.real (A ∩ B) - μ.real B * μ.real A ≤ α := by
    have := (le_abs_self _).trans hAB
    linarith [mul_comm (μ.real A) (μ.real B)]
  have hmid : ∫ ω in A, Y ω ∂μ - μ.real A * ∫ ω, Y ω ∂μ ≤ 2 * b * α := by
    have h1 : ∫ ω in A, Y ω ∂μ - μ.real A * ∫ ω, Y ω ∂μ
        ≤ |∫ ω in A, Y ω ∂μ - (∫ ω, Y ω ∂μ) * μ.real A| := by
      rw [mul_comm (μ.real A)]
      exact le_abs_self _
    have h2 : 2 * b * (μ.real (A ∩ B) - μ.real B * μ.real A) ≤ 2 * b * α :=
      mul_le_mul_of_nonneg_left hAB' (by positivity)
    linarith
  rw [hcov]
  calc |∫ ω, X ω * Y ω ∂μ - (∫ ω, X ω ∂μ) * ∫ ω, Y ω ∂μ|
      ≤ 2 * a * (∫ ω in A, Y ω ∂μ - μ.real A * ∫ ω, Y ω ∂μ) := hstepA
    _ ≤ 2 * a * (2 * b * α) := mul_le_mul_of_nonneg_left hmid (by positivity)
    _ = 4 * α * a * b := by ring
