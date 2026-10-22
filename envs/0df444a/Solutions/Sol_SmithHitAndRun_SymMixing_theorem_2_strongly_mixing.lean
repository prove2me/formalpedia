-- Prove2me | solution 1 for SmithHitAndRun.SymMixing.theorem_2_strongly_mixing
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-22T05:58:46.439746+00:00
-- url     : https://prove2.me/submissions/0065f1a7-4577-411d-bae4-f5043bc41dc9

import Mathlib.Probability.Kernel.Composition.IntegralCompProd
import Mathlib.Probability.Kernel.Invariance
import Definitions.Def_MarkovIterKernel
import Definitions.Def_SmithHitAndRun_SymMixing_uniformLaw
import Definitions.Def_SmithHitAndRun_SymMixing_IsSymmetricMixingKernel

open MeasureTheory ProbabilityTheory Filter


namespace SmithHitAndRun.SymMixing

section Main
variable {α : Type*} [MeasurableSpace α] {V : Measure α} [IsFiniteMeasure V]
  {P : Kernel α α} [IsMarkovKernel P] {f : α → α → ENNReal}

lemma meas_f_left (h : IsSymmetricMixingKernel V P f) (x : α) : Measurable (fun y => f y x) :=
  (h.1.comp (measurable_id.prodMk measurable_const) : _)

lemma P_eq_wd (h : IsSymmetricMixingKernel V P f) (x : α) :
    P x = V.withDensity (fun y => f y x) := by
  ext B hB
  rw [h.2.1 x B hB, withDensity_apply _ hB]

lemma lint_P (h : IsSymmetricMixingKernel V P f) (x : α) (u : α → ENNReal) (hu : Measurable u) :
    ∫⁻ y, u y ∂P x = ∫⁻ y, f y x * u y ∂V := by
  rw [P_eq_wd h x, lintegral_withDensity_eq_lintegral_mul _ (meas_f_left h x) hu]; rfl

lemma adjoint (h : IsSymmetricMixingKernel V P f) (u v : α → ENNReal) (hu : Measurable u)
    (hv : Measurable v) :
    ∫⁻ x, (∫⁻ y, u y ∂P x) * v x ∂V = ∫⁻ y, u y * ∫⁻ x, v x ∂P y ∂V := by
  have hf := h.1
  have hsym := h.2.2
  have e1 : ∀ x, (∫⁻ y, u y ∂P x) * v x = ∫⁻ y, f y x * u y * v x ∂V := by
    intro x
    have hm : Measurable (fun y => f y x * u y) := (meas_f_left h x).mul hu
    rw [lint_P h x u hu, ← lintegral_mul_const (μ := V) (v x) hm]
  have e2 : ∀ y, u y * ∫⁻ x, v x ∂P y = ∫⁻ x, f y x * u y * v x ∂V := by
    intro y
    have hm : Measurable (fun x => f x y * v x) := (meas_f_left h y).mul hv
    rw [lint_P h y v hv, ← lintegral_const_mul (μ := V) (u y) hm]
    refine lintegral_congr (fun x => ?_)
    rw [← hsym x y]; ring
  simp_rw [e1, e2]
  exact lintegral_lintegral_swap
    (((hf.comp measurable_swap).mul (hu.comp measurable_snd)).mul (hv.comp measurable_fst)).aemeasurable

lemma stat_V (h : IsSymmetricMixingKernel V P f) (u : α → ENNReal) (hu : Measurable u) :
    ∫⁻ x, ∫⁻ y, u y ∂P x ∂V = ∫⁻ y, u y ∂V := by
  have := adjoint h u (fun _ => 1) hu measurable_const
  simp only [mul_one, lintegral_const, measure_univ, one_mul] at this
  rw [this]

open MarkovChainCLT in
lemma iter_succ' (P : Kernel α α) (n : ℕ) : iterKernel P (n + 1) = iterKernel P n ∘ₖ P := by
  induction n with
  | zero => simp [iterKernel_succ]
  | succ n ih =>
    calc iterKernel P (n + 1 + 1) = P ∘ₖ iterKernel P (n + 1) := rfl
      _ = P ∘ₖ (iterKernel P n ∘ₖ P) := by rw [ih]
      _ = (P ∘ₖ iterKernel P n) ∘ₖ P := by rw [Kernel.comp_assoc]
      _ = iterKernel P (n + 1) ∘ₖ P := rfl

open MarkovChainCLT in
lemma g_succ (P : Kernel α α) (A : Set α) (hA : MeasurableSet A) (m : ℕ) (x : α) :
    iterKernel P (m + 1) x A = ∫⁻ y, iterKernel P m y A ∂P x := by
  rw [iter_succ', Kernel.comp_apply' _ _ _ hA]


open MarkovChainCLT in
noncomputable def G (P : Kernel α α) (A : Set α) (m : ℕ) (x : α) : ℝ :=
  (iterKernel P m x A).toReal

lemma G_nonneg (P : Kernel α α) (A : Set α) (m : ℕ) (x : α) : 0 ≤ G P A m x :=
  ENNReal.toReal_nonneg

lemma G_le_one (P : Kernel α α) [IsMarkovKernel P] (A : Set α) (m : ℕ) (x : α) : G P A m x ≤ 1 := by
  unfold G
  have := prob_le_one (μ := MarkovChainCLT.iterKernel P m x) (s := A)
  simpa using ENNReal.toReal_mono ENNReal.one_ne_top this

lemma G_meas (P : Kernel α α) [IsMarkovKernel P] {A : Set α} (hA : MeasurableSet A) (m : ℕ) :
    Measurable (G P A m) :=
  (Kernel.measurable_coe _ hA).ennreal_toReal

lemma integrable_of_abs_le {μ : Measure α} [IsFiniteMeasure μ] {u : α → ℝ} (hu : Measurable u)
    (hb : ∀ y, |u y| ≤ 1) : Integrable u μ :=
  Integrable.of_bound hu.aestronglyMeasurable 1 (ae_of_all _ (fun y => by simpa using hb y))

lemma G_succ (P : Kernel α α) [IsMarkovKernel P] {A : Set α} (hA : MeasurableSet A) (m : ℕ) (x : α) :
    G P A (m + 1) x = ∫ y, G P A m y ∂P x := by
  unfold G
  rw [g_succ P A hA]
  rw [integral_toReal (Kernel.measurable_coe _ hA).aemeasurable
    (ae_of_all _ (fun y => lt_of_le_of_lt prob_le_one ENNReal.one_lt_top))]

lemma G_zero (P : Kernel α α) {A : Set α} (hA : MeasurableSet A) (x : α) :
    G P A 0 x = A.indicator (fun _ => (1:ℝ)) x := by
  unfold G
  simp only [MarkovChainCLT.iterKernel_zero, Kernel.id_apply]
  rw [Measure.dirac_apply' _ hA]
  by_cases hx : x ∈ A <;> simp [hx]

lemma sq_integrable {μ : Measure α} [IsFiniteMeasure μ] {u : α → ℝ} (hu : Measurable u)
    (hb : ∀ y, |u y| ≤ 1) : Integrable (fun y => u y ^ 2) μ :=
  integrable_of_abs_le (hu.pow_const 2) (fun y => by
    have := hb y; rw [abs_pow]; nlinarith [abs_nonneg (u y)])

lemma sqsub_integrable {μ : Measure α} [IsFiniteMeasure μ] {u : α → ℝ} (hu : Measurable u)
    (hb : ∀ y, |u y| ≤ 1) (m : ℝ) : Integrable (fun y => (u y - m) ^ 2) μ := by
  have h1 : Integrable u μ := integrable_of_abs_le hu hb
  have h2 := sq_integrable (μ := μ) hu hb
  have i4 : Integrable (fun y => 2 * m * u y) μ := h1.const_mul _
  have i3 : Integrable (fun y => u y ^ 2 - 2 * m * u y) μ := h2.sub i4
  have i5 : Integrable (fun y => u y ^ 2 - 2 * m * u y + m ^ 2) μ := i3.add (integrable_const _)
  have : ∀ y, (u y - m) ^ 2 = u y ^ 2 - 2 * m * u y + m ^ 2 := fun y => by ring
  simp_rw [this]
  exact i5

lemma var_formula {μ : Measure α} [IsProbabilityMeasure μ] {u : α → ℝ} (hu : Measurable u)
    (hb : ∀ y, |u y| ≤ 1) :
    ∫ y, (u y - ∫ z, u z ∂μ) ^ 2 ∂μ = ∫ y, u y ^ 2 ∂μ - (∫ y, u y ∂μ) ^ 2 := by
  set m := ∫ z, u z ∂μ with hm
  have h1 : Integrable u μ := integrable_of_abs_le hu hb
  have h2 := sq_integrable (μ := μ) hu hb
  have i4 : Integrable (fun y => 2 * m * u y) μ := h1.const_mul _
  have i3 : Integrable (fun y => u y ^ 2 - 2 * m * u y) μ := h2.sub i4
  have : ∀ y, (u y - m) ^ 2 = u y ^ 2 - 2 * m * u y + m ^ 2 := fun y => by ring
  simp_rw [this]
  rw [integral_add i3 (integrable_const _), integral_sub h2 i4,
    integral_const_mul]
  simp [hm]
  ring

lemma jensen {μ : Measure α} [IsProbabilityMeasure μ] {u : α → ℝ} (hu : Measurable u)
    (hb : ∀ y, |u y| ≤ 1) : (∫ y, u y ∂μ) ^ 2 ≤ ∫ y, u y ^ 2 ∂μ := by
  have := var_formula (μ := μ) hu hb
  have h0 : 0 ≤ ∫ y, (u y - ∫ z, u z ∂μ) ^ 2 ∂μ := integral_nonneg (fun y => sq_nonneg _)
  linarith

lemma var_zero {μ : Measure α} [IsProbabilityMeasure μ] {u : α → ℝ} (hu : Measurable u)
    (hb : ∀ y, |u y| ≤ 1) (he : (∫ y, u y ∂μ) ^ 2 = ∫ y, u y ^ 2 ∂μ) :
    ∀ᵐ y ∂μ, u y = ∫ z, u z ∂μ := by
  have h := var_formula (μ := μ) hu hb
  have h0 : ∫ y, (u y - ∫ z, u z ∂μ) ^ 2 ∂μ = 0 := by linarith
  have := (integral_eq_zero_iff_of_nonneg (fun y => sq_nonneg _)
    (sqsub_integrable (μ := μ) hu hb _)).1 h0
  filter_upwards [this] with y hy
  have : (u y - ∫ z, u z ∂μ) ^ 2 = 0 := hy
  exact sub_eq_zero.1 (pow_eq_zero_iff (two_ne_zero)|>.1 this)

lemma invariant_V (h : IsSymmetricMixingKernel V P f) : Kernel.Invariant P V := by
  unfold Kernel.Invariant
  ext B hB
  rw [Measure.bind_apply hB P.measurable.aemeasurable]
  have := stat_V h (B.indicator 1) (measurable_one.indicator hB)
  simpa [lintegral_indicator_one hB] using this

lemma stat_real (h : IsSymmetricMixingKernel V P f) {u : α → ℝ} (hu : Measurable u)
    (hb : ∀ y, |u y| ≤ 1) :
    ∫ x, ∫ y, u y ∂P x ∂V = ∫ y, u y ∂V := by
  have hinv := invariant_V h
  have hint : Integrable u ((P ∘ₖ Kernel.const Unit V) ()) := by
    rw [Kernel.comp_apply, Kernel.const_apply, hinv.def]
    exact integrable_of_abs_le hu hb
  have e1 := Kernel.integral_comp (η := P) (κ := Kernel.const Unit V) (a := ()) hint
  rw [Kernel.comp_apply, Kernel.const_apply, hinv.def] at e1
  exact e1.symm

lemma T_meas (P : Kernel α α) {u : α → ℝ} (hu : Measurable u) :
    Measurable (fun x => ∫ y, u y ∂P x) :=
  (hu.stronglyMeasurable.integral_kernel (κ := P)).measurable

lemma T_abs (P : Kernel α α) [IsMarkovKernel P] {u : α → ℝ} (hb : ∀ y, |u y| ≤ 1) (x : α) :
    |∫ y, u y ∂P x| ≤ 1 := by
  have := norm_integral_le_of_norm_le_const (μ := P x) (f := u) (C := 1)
    (ae_of_all _ (fun y => by simpa using hb y))
  simpa using this

lemma G_abs (P : Kernel α α) [IsMarkovKernel P] (A : Set α) (m : ℕ) (x : α) :
    |G P A m x| ≤ 1 := by
  rw [abs_of_nonneg (G_nonneg P A m x)]; exact G_le_one P A m x

lemma G_sq_abs (P : Kernel α α) [IsMarkovKernel P] (A : Set α) (m : ℕ) (x : α) :
    |G P A m x ^ 2| ≤ 1 := by
  have := G_abs P A m x
  rw [abs_pow]; nlinarith [abs_nonneg (G P A m x)]

/-- Real inner product of iterates. -/
noncomputable def R (P : Kernel α α) (V : Measure α) (A : Set α) (m n : ℕ) : ℝ :=
  ∫ x, G P A m x * G P A n x ∂V

lemma R_succ (h : IsSymmetricMixingKernel V P f) {A : Set α} (hA : MeasurableSet A) (m n : ℕ) :
    R P V A (m + 1) n = R P V A m (n + 1) := by
  have hg : ∀ k, Measurable (fun x => MarkovChainCLT.iterKernel P k x A) :=
    fun k => Kernel.measurable_coe _ hA
  have hR : ∀ m n, R P V A m n =
      (∫⁻ x, MarkovChainCLT.iterKernel P m x A * MarkovChainCLT.iterKernel P n x A ∂V).toReal := by
    intro m n
    unfold R G
    have := integral_toReal (μ := V)
      (f := fun x => MarkovChainCLT.iterKernel P m x A * MarkovChainCLT.iterKernel P n x A)
      ((hg m).mul (hg n)).aemeasurable
      (ae_of_all _ (fun x => ENNReal.mul_lt_top
        (lt_of_le_of_lt prob_le_one ENNReal.one_lt_top)
        (lt_of_le_of_lt prob_le_one ENNReal.one_lt_top)))
    simp_rw [ENNReal.toReal_mul] at this
    exact this
  rw [hR, hR]
  congr 1
  have := adjoint h (fun y => MarkovChainCLT.iterKernel P m y A)
    (fun y => MarkovChainCLT.iterKernel P n y A) (hg m) (hg n)
  simp_rw [← g_succ P A hA] at this
  exact this

lemma R_eq (h : IsSymmetricMixingKernel V P f) {A : Set α} (hA : MeasurableSet A) (m n : ℕ) :
    R P V A m n = R P V A (m + n) 0 := by
  induction m generalizing n with
  | zero =>
    simp only [zero_add]
    unfold R
    simp_rw [mul_comm]
  | succ m ih =>
    rw [R_succ h hA, ih (n + 1)]
    congr 1; omega

lemma R_contr (h : IsSymmetricMixingKernel V P f) {A : Set α} (hA : MeasurableSet A) (i : ℕ) :
    R P V A (i + 1) (i + 1) ≤ R P V A i i := by
  unfold R
  have hm : ∀ k, Measurable (G P A k) := fun k => G_meas P hA k
  have e1 : ∀ x, G P A (i + 1) x * G P A (i + 1) x = (∫ y, G P A i y ∂P x) ^ 2 := by
    intro x; rw [G_succ P hA, sq]
  have e2 : ∀ x, G P A i x * G P A i x = G P A i x ^ 2 := fun x => (sq _).symm
  simp_rw [e1, e2]
  calc ∫ x, (∫ y, G P A i y ∂P x) ^ 2 ∂V ≤ ∫ x, ∫ y, G P A i y ^ 2 ∂P x ∂V := by
        refine integral_mono ?_ ?_ (fun x => jensen (hm i) (G_abs P A i))
        · exact integrable_of_abs_le ((T_meas P (hm i)).pow_const 2) (fun x => by
            have := T_abs P (G_abs P A i) x
            rw [abs_pow]; nlinarith [abs_nonneg (∫ y, G P A i y ∂P x)])
        · exact integrable_of_abs_le (T_meas P ((hm i).pow_const 2)) (T_abs P (G_sq_abs P A i))
    _ = ∫ x, G P A i x ^ 2 ∂V := stat_real h ((hm i).pow_const 2) (G_sq_abs P A i)

lemma small_integral (h : IsSymmetricMixingKernel V P f) (x : α) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ u : α → ℝ, Measurable u → (∀ y, |u y| ≤ 1) → ∫ y, u y ^ 2 ∂V < δ →
      |∫ y, u y ∂P x| < ε := by
  set e := ε / 2 with he
  have he0 : 0 < e := by positivity
  have hfin : ∫⁻ y, f y x ∂V ≠ ⊤ := by
    have := h.2.1 x Set.univ MeasurableSet.univ
    rw [Measure.restrict_univ] at this
    rw [← this]; exact measure_ne_top _ _
  obtain ⟨δ₀, hδ₀pos, hδ₀⟩ := exists_pos_setLIntegral_lt_of_measure_lt (μ := V)
    (f := fun y => f y x) hfin (ε := ENNReal.ofReal e) (by simpa using he0)
  have hmin0 : 0 < min δ₀ 1 := lt_min hδ₀pos one_pos
  have hmint : min δ₀ 1 ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top (min_le_right _ _)
  set δ₁ : ℝ := (min δ₀ 1).toReal with hδ₁
  have hδ₁pos : 0 < δ₁ := ENNReal.toReal_pos hmin0.ne' hmint
  have hofδ₁ : ENNReal.ofReal δ₁ ≤ δ₀ := by
    rw [hδ₁, ENNReal.ofReal_toReal hmint]; exact min_le_left _ _
  refine ⟨e ^ 2 * δ₁, by positivity, fun u hu hb hint => ?_⟩
  set S : Set α := {y | e ^ 2 ≤ u y ^ 2} with hS
  have hSm : MeasurableSet S := measurableSet_le measurable_const (hu.pow_const 2)
  have hcheb := mul_meas_ge_le_integral_of_nonneg (μ := V) (f := fun y => u y ^ 2)
    (ae_of_all _ (fun y => sq_nonneg _)) (sq_integrable hu hb) (e ^ 2)
  have hVS : V.real S < δ₁ := by
    have : e ^ 2 * V.real S < e ^ 2 * δ₁ := lt_of_le_of_lt hcheb hint
    exact lt_of_mul_lt_mul_left this (by positivity)
  have hVS' : V S < δ₀ := by
    have h1 : V S < ENNReal.ofReal δ₁ :=
      (ENNReal.lt_ofReal_iff_toReal_lt (measure_ne_top _ _)).2 hVS
    exact lt_of_lt_of_le h1 hofδ₁
  have hPS : (P x).real S < e := by
    have h1 := hδ₀ S hVS'
    rw [← h.2.1 x S hSm] at h1
    exact ENNReal.toReal_lt_of_lt_ofReal h1
  have hbound : ∀ y, ‖u y‖ ≤ e + S.indicator (fun _ => (1:ℝ)) y := by
    intro y
    by_cases hy : y ∈ S
    · simp only [Set.indicator_of_mem hy, Real.norm_eq_abs]
      have := hb y; linarith
    · simp only [Set.indicator_of_notMem hy, Real.norm_eq_abs, add_zero]
      have : u y ^ 2 < e ^ 2 := by simpa [hS] using hy
      exact le_of_lt (abs_lt_of_sq_lt_sq this he0.le)
  have hintg : Integrable (fun y => e + S.indicator (fun _ => (1:ℝ)) y) (P x) :=
    (integrable_const _).add ((integrable_const (1:ℝ)).indicator hSm)
  have := norm_integral_le_of_norm_le hintg (ae_of_all _ hbound)
  rw [integral_add (integrable_const _) ((integrable_const (1:ℝ)).indicator hSm)] at this
  have h2 : ∫ y, S.indicator (fun _ => (1:ℝ)) y ∂P x = (P x).real S := by
    rw [integral_indicator hSm]; simp
  rw [h2] at this
  simp only [integral_const, smul_eq_mul] at this
  have hu1 : (P x).real Set.univ = 1 := by simp
  rw [hu1, one_mul, Real.norm_eq_abs] at this
  linarith

lemma prod_integrable (P : Kernel α α) [IsMarkovKernel P] {A : Set α} (hA : MeasurableSet A)
    {μ : Measure α} [IsFiniteMeasure μ] (m n : ℕ) :
    Integrable (fun x => G P A m x * G P A n x) μ :=
  integrable_of_abs_le ((G_meas P hA m).mul (G_meas P hA n)) (fun x => by
    rw [abs_mul]
    exact mul_le_one₀ (G_abs P A m x) (abs_nonneg _) (G_abs P A n x))

lemma d_formula (P : Kernel α α) [IsMarkovKernel P] {A : Set α} (hA : MeasurableSet A) (m n : ℕ) :
    ∫ x, (G P A m x - G P A n x) ^ 2 ∂V = R P V A m m - 2 * R P V A m n + R P V A n n := by
  unfold R
  have i1 := prod_integrable P hA (μ := V) m m
  have i2 := prod_integrable P hA (μ := V) m n
  have i3 := prod_integrable P hA (μ := V) n n
  have i4 : Integrable (fun x => 2 * (G P A m x * G P A n x)) V := i2.const_mul _
  have i5 : Integrable (fun x => G P A m x * G P A m x - 2 * (G P A m x * G P A n x)) V := i1.sub i4
  have : ∀ x, (G P A m x - G P A n x) ^ 2 =
      G P A m x * G P A m x - 2 * (G P A m x * G P A n x) + G P A n x * G P A n x :=
    fun x => by ring
  simp_rw [this]
  rw [integral_add i5 i3, integral_sub i1 i4, integral_const_mul]

lemma R_nonneg (P : Kernel α α) [IsMarkovKernel P] (A : Set α) (m : ℕ) :
    0 ≤ R P V A m m :=
  integral_nonneg (fun x => mul_nonneg (G_nonneg P A m x) (G_nonneg P A m x))

lemma R_anti (h : IsSymmetricMixingKernel V P f) {A : Set α} (hA : MeasurableSet A) :
    Antitone (fun i => R P V A i i) :=
  antitone_nat_of_succ_le (fun i => R_contr h hA i)

lemma d_le (h : IsSymmetricMixingKernel V P f) {A : Set α} (hA : MeasurableSet A) {j k : ℕ}
    (hjk : j ≤ k) :
    ∫ x, (G P A (2 * j) x - G P A (2 * k) x) ^ 2 ∂V ≤
      R P V A (2 * j) (2 * j) - R P V A (2 * k) (2 * k) := by
  rw [d_formula P hA]
  have e : R P V A (2 * j) (2 * k) = R P V A (j + k) (j + k) := by
    rw [R_eq h hA, R_eq h hA (j + k)]; congr 1; omega
  have : R P V A (2 * k) (2 * k) ≤ R P V A (j + k) (j + k) :=
    R_anti h hA (by omega)
  rw [e]; linarith

lemma pointwise_cauchy (h : IsSymmetricMixingKernel V P f) {A : Set α} (hA : MeasurableSet A)
    (x : α) : CauchySeq (fun j : ℕ => G P A (2 * j + 1) x) := by
  rw [Metric.cauchySeq_iff]
  intro ε hε
  obtain ⟨δ, hδ, hδu⟩ := small_integral h x hε
  obtain ⟨L, hL⟩ : ∃ L, Tendsto (fun i => R P V A i i) atTop (nhds L) :=
    ⟨_, tendsto_atTop_ciInf (R_anti h hA) ⟨0, fun _ ⟨i, hi⟩ => hi ▸ R_nonneg P A i⟩⟩
  have hLle : ∀ i, L ≤ R P V A i i := fun i => (R_anti h hA).le_of_tendsto hL i
  obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.1 hL) δ hδ
  have key : ∀ j k, N ≤ j → j ≤ k → |G P A (2 * j + 1) x - G P A (2 * k + 1) x| < ε := by
    intro j k hj hjk
    have h1 : ∫ y, (G P A (2 * j) y - G P A (2 * k) y) ^ 2 ∂V < δ := by
      have := d_le h hA hjk
      have h2 := hN (2 * j) (by omega)
      have h3 := hLle (2 * k)
      rw [Real.dist_eq] at h2
      have h4 := (abs_lt.1 h2).2
      linarith
    have h5 := hδu (fun y => G P A (2 * j) y - G P A (2 * k) y)
      ((G_meas P hA _).sub (G_meas P hA _))
      (fun y => by
        have a1 := G_nonneg P A (2 * j) y; have a2 := G_le_one P A (2 * j) y
        have b1 := G_nonneg P A (2 * k) y; have b2 := G_le_one P A (2 * k) y
        rw [abs_le]; constructor <;> linarith) h1
    have e : ∫ y, (G P A (2 * j) y - G P A (2 * k) y) ∂P x =
        G P A (2 * j + 1) x - G P A (2 * k + 1) x := by
      rw [integral_sub (integrable_of_abs_le (G_meas P hA _) (G_abs P A _))
        (integrable_of_abs_le (G_meas P hA _) (G_abs P A _)), G_succ P hA, G_succ P hA]
    rw [e] at h5
    exact h5
  refine ⟨N, fun j hj k hk => ?_⟩
  rw [Real.dist_eq]
  rcases le_total j k with hjk | hkj
  · exact key j k hj hjk
  · rw [abs_sub_comm]; exact key k j hk hkj

lemma dct_lemma {μ : Measure α} [IsFiniteMeasure μ] {F : ℕ → α → ℝ} {φ : α → ℝ}
    (hF : ∀ n, Measurable (F n)) (hb : ∀ n y, |F n y| ≤ 1)
    (hlim : ∀ y, Tendsto (fun n => F n y) atTop (nhds (φ y))) :
    Tendsto (fun n => ∫ y, F n y ∂μ) atTop (nhds (∫ y, φ y ∂μ)) :=
  tendsto_integral_of_dominated_convergence (fun _ => 1) (fun n => (hF n).aestronglyMeasurable)
    (integrable_const 1) (fun n => ae_of_all _ (fun y => by simpa using hb n y))
    (ae_of_all _ hlim)

lemma exists_h (h : IsSymmetricMixingKernel V P f) {A : Set α} (hA : MeasurableSet A) :
    ∃ h₀ h₁ : α → ℝ, Measurable h₀ ∧ Measurable h₁ ∧ (∀ y, 0 ≤ h₀ y ∧ h₀ y ≤ 1) ∧
      (∀ y, 0 ≤ h₁ y ∧ h₁ y ≤ 1) ∧
      (∀ x, Tendsto (fun j : ℕ => G P A (2 * j) x) atTop (nhds (h₀ x))) ∧
      (∀ x, Tendsto (fun j : ℕ => G P A (2 * j + 1) x) atTop (nhds (h₁ x))) ∧
      (∀ x, h₀ x = ∫ y, h₁ y ∂P x) ∧ (∀ x, h₁ x = ∫ y, h₀ y ∂P x) := by
  classical
  set h₁ : α → ℝ := fun x => limUnder atTop (fun j : ℕ => G P A (2 * j + 1) x) with hh₁
  have t1 : ∀ x, Tendsto (fun j : ℕ => G P A (2 * j + 1) x) atTop (nhds (h₁ x)) :=
    fun x => (pointwise_cauchy h hA x).tendsto_limUnder
  have m1 : Measurable h₁ :=
    measurable_of_tendsto_metrizable (fun j => G_meas P hA (2 * j + 1))
      (tendsto_pi_nhds.2 t1)
  have b1 : ∀ y, 0 ≤ h₁ y ∧ h₁ y ≤ 1 := fun y =>
    ⟨ge_of_tendsto' (t1 y) (fun j => G_nonneg P A _ y), le_of_tendsto' (t1 y) (fun j => G_le_one P A _ y)⟩
  set h₀ : α → ℝ := fun x => ∫ y, h₁ y ∂P x with hh₀
  have m0 : Measurable h₀ := T_meas P m1
  have t0' : ∀ x, Tendsto (fun j : ℕ => G P A (2 * j + 1 + 1) x) atTop (nhds (h₀ x)) := by
    intro x
    have := dct_lemma (μ := P x) (F := fun j y => G P A (2 * j + 1) y) (φ := h₁)
      (fun j => G_meas P hA _) (fun j y => G_abs P A _ y) t1
    simpa [G_succ P hA] using this
  have t0 : ∀ x, Tendsto (fun j : ℕ => G P A (2 * j) x) atTop (nhds (h₀ x)) := by
    intro x
    rw [← tendsto_add_atTop_iff_nat 1]
    have e : ∀ j : ℕ, 2 * (j + 1) = 2 * j + 1 + 1 := fun j => by omega
    simp_rw [e]
    exact t0' x
  have b0 : ∀ y, 0 ≤ h₀ y ∧ h₀ y ≤ 1 := fun y =>
    ⟨ge_of_tendsto' (t0 y) (fun j => G_nonneg P A _ y), le_of_tendsto' (t0 y) (fun j => G_le_one P A _ y)⟩
  have e1 : ∀ x, h₁ x = ∫ y, h₀ y ∂P x := by
    intro x
    have := dct_lemma (μ := P x) (F := fun j y => G P A (2 * j) y) (φ := h₀)
      (fun j => G_meas P hA _) (fun j y => G_abs P A _ y) t0
    have h2 : Tendsto (fun j : ℕ => G P A (2 * j + 1) x) atTop (nhds (∫ y, h₀ y ∂P x)) := by
      simpa [G_succ P hA] using this
    exact tendsto_nhds_unique (t1 x) h2
  exact ⟨h₀, h₁, m0, m1, b0, b1, t0, t1, fun x => rfl, e1⟩

lemma abs_sq_le_one' {u : α → ℝ} (hb : ∀ y, |u y| ≤ 1) (y : α) : |u y ^ 2| ≤ 1 := by
  have := hb y; rw [abs_pow]; nlinarith [abs_nonneg (u y)]

lemma T_integrable (P : Kernel α α) [IsMarkovKernel P] {μ : Measure α} [IsFiniteMeasure μ]
    {u : α → ℝ} (hu : Measurable u) (hb : ∀ y, |u y| ≤ 1) :
    Integrable (fun x => ∫ y, u y ∂P x) μ :=
  integrable_of_abs_le (T_meas P hu) (T_abs P hb)

lemma key_pos (h : IsSymmetricMixingKernel V P f) (hpos : ∀ x y, 0 < f y x)
    (B : Set α) (hB : MeasurableSet B) (hVB : V B ≠ 0) (z : α) : 0 < P z B := by
  obtain ⟨hf, hP, hsym⟩ := h
  rw [pos_iff_ne_zero]
  intro h0
  rw [hP z B hB] at h0
  have hm : Measurable (fun y => f y z) := by
    have : Measurable (fun y => Function.uncurry f (y, z)) :=
      hf.comp (measurable_id.prodMk measurable_const)
    exact this
  rw [lintegral_eq_zero_iff hm] at h0
  have h2 : ∀ᵐ y ∂(V.restrict B), False :=
    h0.mono (fun y hy => by have := hpos z y; simp only [Pi.zero_apply] at hy; rw [hy] at this; exact lt_irrefl _ this)
  simp only [Filter.eventually_false_iff_eq_bot, ae_eq_bot, Measure.restrict_eq_zero] at h2
  exact hVB h2

lemma const_of_harmonic (h : IsSymmetricMixingKernel V P f) (hpos : ∀ x y, 0 < f y x)
    (hV : V ≠ 0) {h₀ h₁ : α → ℝ} (m0 : Measurable h₀) (m1 : Measurable h₁)
    (b0 : ∀ y, |h₀ y| ≤ 1) (b1 : ∀ y, |h₁ y| ≤ 1)
    (e0 : ∀ x, h₀ x = ∫ y, h₁ y ∂P x) (e1 : ∀ x, h₁ x = ∫ y, h₀ y ∂P x) :
    ∃ m : ℝ, (∀ x, h₀ x = m) ∧ (∀ x, h₁ x = m) := by
  -- chain of inequalities
  have step : ∀ {u : α → ℝ}, Measurable u → (∀ y, |u y| ≤ 1) →
      ∫ x, (∫ y, u y ∂P x) ^ 2 ∂V ≤ ∫ x, ∫ y, u y ^ 2 ∂P x ∂V := by
    intro u hu hb
    refine integral_mono ?_ ?_ (fun x => jensen hu hb)
    · exact integrable_of_abs_le ((T_meas P hu).pow_const 2) (fun x => by
        have := T_abs P hb x
        rw [abs_pow]; nlinarith [abs_nonneg (∫ y, u y ∂P x)])
    · exact T_integrable P (hu.pow_const 2) (abs_sq_le_one' hb)
  have s1 := step m1 b1
  have s0 := step m0 b0
  rw [stat_real h (m1.pow_const 2) (abs_sq_le_one' b1)] at s1
  rw [stat_real h (m0.pow_const 2) (abs_sq_le_one' b0)] at s0
  have r0 : ∫ x, (∫ y, h₁ y ∂P x) ^ 2 ∂V = ∫ x, h₀ x ^ 2 ∂V := by simp_rw [← e0]
  have r1 : ∫ x, (∫ y, h₀ y ∂P x) ^ 2 ∂V = ∫ x, h₁ x ^ 2 ∂V := by simp_rw [← e1]
  rw [r0] at s1
  rw [r1] at s0
  have heq : ∫ x, (∫ y, h₀ y ∂P x) ^ 2 ∂V = ∫ x, ∫ y, h₀ y ^ 2 ∂P x ∂V := by
    rw [stat_real h (m0.pow_const 2) (abs_sq_le_one' b0), r1]
    exact le_antisymm s0 s1
  -- conclude ae equality
  have iA : Integrable (fun x => ∫ y, h₀ y ^ 2 ∂P x) V := T_integrable P (m0.pow_const 2) (abs_sq_le_one' b0)
  have iB : Integrable (fun x => (∫ y, h₀ y ∂P x) ^ 2) V :=
    integrable_of_abs_le ((T_meas P m0).pow_const 2) (fun x => by
      have := T_abs P b0 x
      rw [abs_pow]; nlinarith [abs_nonneg (∫ y, h₀ y ∂P x)])
  have h0 : ∫ x, (∫ y, h₀ y ^ 2 ∂P x - (∫ y, h₀ y ∂P x) ^ 2) ∂V = 0 := by
    rw [integral_sub iA iB, heq]; ring
  have hae := (integral_eq_zero_iff_of_nonneg (fun x => sub_nonneg.2 (jensen m0 b0)) (iA.sub iB)).1 h0
  have : NeBot (ae V) := ae_neBot.2 hV
  obtain ⟨x₀, hx₀⟩ := hae.exists
  have hx₀' : (∫ y, h₀ y ∂P x₀) ^ 2 = ∫ y, h₀ y ^ 2 ∂P x₀ := by
    have : ∫ y, h₀ y ^ 2 ∂P x₀ - (∫ y, h₀ y ∂P x₀) ^ 2 = 0 := hx₀
    linarith
  have hvz := var_zero (μ := P x₀) m0 b0 hx₀'
  set m := ∫ y, h₀ y ∂P x₀ with hm
  have hVae : ∀ᵐ y ∂V, h₀ y = m := by
    by_contra hcon
    have hB : MeasurableSet {y | h₀ y ≠ m} := (m0 (measurableSet_singleton m)).compl
    have hVB : V {y | h₀ y ≠ m} ≠ 0 := by
      intro h0'
      apply hcon
      rw [ae_iff]; exact h0'
    have := key_pos h hpos _ hB hVB x₀
    have h2 : P x₀ {y | h₀ y ≠ m} = 0 := by
      rw [ae_iff] at hvz; exact hvz
    rw [h2] at this; exact lt_irrefl _ this
  have hac : ∀ x, P x ≪ V := fun x => by
    rw [P_eq_wd h x]; exact withDensity_absolutelyContinuous _ _
  have hh1 : ∀ x, h₁ x = m := by
    intro x
    rw [e1 x]
    have : ∀ᵐ y ∂P x, h₀ y = m := (hac x).ae_le hVae
    rw [integral_congr_ae this]; simp
  refine ⟨m, fun x => ?_, hh1⟩
  rw [e0 x]
  simp_rw [hh1]; simp

lemma int_G (h : IsSymmetricMixingKernel V P f) {A : Set α} (hA : MeasurableSet A) (k : ℕ) :
    ∫ x, G P A k x ∂V = V.real A := by
  induction k with
  | zero =>
    simp_rw [G_zero P hA]
    exact integral_indicator_one (μ := V) hA
  | succ k ih =>
    simp_rw [G_succ P hA]
    rw [stat_real h (G_meas P hA k) (G_abs P A k), ih]

lemma tendsto_of_even_odd {u : ℕ → ℝ} {l : ℝ}
    (he : Tendsto (fun j : ℕ => u (2 * j)) atTop (nhds l))
    (ho : Tendsto (fun j : ℕ => u (2 * j + 1)) atTop (nhds l)) :
    Tendsto u atTop (nhds l) := by
  rw [Metric.tendsto_atTop] at he ho ⊢
  intro ε hε
  obtain ⟨N₁, h1⟩ := he ε hε
  obtain ⟨N₂, h2⟩ := ho ε hε
  refine ⟨2 * (max N₁ N₂) + 2, fun k hk => ?_⟩
  obtain ⟨j, hj | hj⟩ := Nat.even_or_odd' k
  · subst hj; exact h1 j (by have := le_max_left N₁ N₂; omega)
  · subst hj; exact h2 j (by have := le_max_right N₁ N₂; omega)

theorem theorem2_core {α : Type*} [MeasurableSpace α]
    (V : Measure α) [IsFiniteMeasure V] (hV : V ≠ 0)
    (P : Kernel α α) [IsMarkovKernel P] (f : α → α → ENNReal)
    (h : IsSymmetricMixingKernel V P f) (hpos : ∀ x y, 0 < f y x) :
    ∀ x : α, ∀ A : Set α, MeasurableSet A →
      Tendsto (fun m : ℕ => MarkovChainCLT.iterKernel P m x A)
        atTop (nhds (uniformLaw V A)) := by
  intro x A hA
  obtain ⟨h₀, h₁, m0, m1, b0, b1, t0, t1, e0, e1⟩ := exists_h h hA
  obtain ⟨m, hm0, hm1⟩ := const_of_harmonic h hpos hV m0 m1
    (fun y => by rw [abs_of_nonneg (b0 y).1]; exact (b0 y).2)
    (fun y => by rw [abs_of_nonneg (b1 y).1]; exact (b1 y).2) e0 e1
  have hmV : m * V.real Set.univ = V.real A := by
    have := dct_lemma (μ := V) (F := fun j y => G P A (2 * j) y) (φ := fun _ => m)
      (fun j => G_meas P hA _) (fun j y => G_abs P A _ y)
      (fun y => by simpa [hm0 y] using t0 y)
    simp_rw [int_G h hA] at this
    have h2 := tendsto_nhds_unique this tendsto_const_nhds
    simp only [integral_const, smul_eq_mul] at h2
    linarith
  have hG : Tendsto (fun k : ℕ => G P A k x) atTop (nhds m) := by
    apply tendsto_of_even_odd
    · simpa [hm0 x] using t0 x
    · simpa [hm1 x] using t1 x
  have hVu : V Set.univ ≠ 0 := fun h0 => hV (Measure.measure_univ_eq_zero.1 h0)
  have hVt : V Set.univ ≠ ⊤ := measure_ne_top _ _
  have hm_nonneg : 0 ≤ m := ge_of_tendsto' hG (fun k => G_nonneg P A k x)
  have hlaw : uniformLaw V A = ENNReal.ofReal m := by
    unfold uniformLaw
    simp only [Measure.smul_apply, smul_eq_mul]
    have hr : ENNReal.ofReal m * V Set.univ = V A := by
      have h1 : ENNReal.ofReal (m * V.real Set.univ) = ENNReal.ofReal (V.real A) := by rw [hmV]
      rw [ENNReal.ofReal_mul hm_nonneg] at h1
      simpa [Measure.real, ENNReal.ofReal_toReal (measure_ne_top V _)] using h1
    rw [← hr, ← mul_assoc, mul_comm _ (ENNReal.ofReal m), mul_assoc, ENNReal.inv_mul_cancel hVu hVt, mul_one]
  rw [hlaw]
  have : ∀ k : ℕ, MarkovChainCLT.iterKernel P k x A = ENNReal.ofReal (G P A k x) := fun k => by
    unfold G; rw [ENNReal.ofReal_toReal (measure_ne_top _ _)]
  simp_rw [this]
  exact (ENNReal.tendsto_ofReal hG)

end Main
end SmithHitAndRun.SymMixing

open SmithHitAndRun.SymMixing


theorem solution {α : Type*} [MeasurableSpace α]
    (V : Measure α) [IsFiniteMeasure V] (hV : V ≠ 0)
    (P : Kernel α α) [IsMarkovKernel P] (f : α → α → ENNReal)
    (h : IsSymmetricMixingKernel V P f) (hpos : ∀ x y, 0 < f y x) :
    ∀ x : α, ∀ A : Set α, MeasurableSet A →
      Tendsto (fun m : ℕ => MarkovChainCLT.iterKernel P m x A)
        atTop (nhds (uniformLaw V A)) := by
  exact theorem2_core V hV P f h hpos
