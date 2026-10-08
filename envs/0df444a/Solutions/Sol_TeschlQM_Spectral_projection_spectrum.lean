-- Prove2me | solution 1 for TeschlQM.Spectral.projection_spectrum
-- status  : ACCEPTED   (prove)
-- author  : @Gabewhigham
-- created : 2026-10-04T16:42:14.307972+00:00
-- url     : https://prove2.me/submissions/40babd8e-286c-4b45-9899-e4da59f948d3

import Mathlib
import Definitions.Def_TeschlQM_Shared_IsProjValuedMeasure
import Definitions.Def_TeschlQM_Spectral_spectralMeasure
import Definitions.Def_TeschlQM_Spectral_boundedSpectralIntegral
import Definitions.Def_TeschlQM_Spectral_spectralIntegral
import Definitions.Def_TeschlQM_Spectral_spectrum

open MeasureTheory
open scoped ENNReal InnerProductSpace

namespace TeschlQM.Spectral.BFC

open TeschlQM.Shared TeschlQM.Spectral

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {P : Set ℝ → (H →L[ℂ] H)}

/-! ### Elementary properties of projection-valued measures -/

lemma pvm_empty (hP : IsProjValuedMeasure P) : P ∅ = 0 := by
  ext ψ
  have h := hP.2.2 (fun _ => ∅) (fun _ => MeasurableSet.empty)
    (fun i j _ => disjoint_bot_left) ψ
  simp only [Set.iUnion_empty] at h
  have h2 : Filter.Tendsto (fun N : ℕ => ∑ n ∈ Finset.range (N+1), P ∅ ψ -
      ∑ n ∈ Finset.range N, P ∅ ψ) Filter.atTop (nhds (P ∅ ψ - P ∅ ψ)) :=
    (h.comp (Filter.tendsto_add_atTop_nat 1)).sub h
  simp only [Finset.sum_range_succ, add_sub_cancel_left, sub_self] at h2
  simpa using tendsto_nhds_unique tendsto_const_nhds h2

lemma pvm_union (hP : IsProjValuedMeasure P) {A B : Set ℝ} (hA : MeasurableSet A)
    (hB : MeasurableSet B) (hAB : Disjoint A B) : P (A ∪ B) = P A + P B := by
  ext ψ
  let Ω : ℕ → Set ℝ := fun n => if n = 0 then A else if n = 1 then B else ∅
  have hΩm : ∀ n, MeasurableSet (Ω n) := by
    intro n; simp only [Ω]; split_ifs <;> simp [hA, hB]
  have hΩd : Pairwise (Function.onFun Disjoint Ω) := by
    intro i j hij
    simp only [Function.onFun, Ω]
    split_ifs <;> first | omega | simp_all [disjoint_comm]
  have hU : (⋃ n, Ω n) = A ∪ B := by
    ext x; simp only [Set.mem_iUnion, Set.mem_union, Ω]
    constructor
    · rintro ⟨n, hn⟩; split_ifs at hn <;> simp_all
    · rintro (h | h)
      · exact ⟨0, by simpa using h⟩
      · exact ⟨1, by simpa using h⟩
  have h := hP.2.2 Ω hΩm hΩd ψ
  rw [hU] at h
  have hev : ∀ N, 2 ≤ N → ∑ n ∈ Finset.range N, P (Ω n) ψ = P A ψ + P B ψ := by
    intro N hN
    induction N, hN using Nat.le_induction with
    | base => simp [Finset.sum_range_succ, Ω]
    | succ N hN ih =>
      rw [Finset.sum_range_succ, ih]
      have : Ω N = ∅ := by simp only [Ω]; split_ifs <;> first | omega | rfl
      simp [this, pvm_empty hP]
  have h2 : Filter.Tendsto (fun N : ℕ => ∑ n ∈ Finset.range N, P (Ω n) ψ) Filter.atTop
      (nhds (P A ψ + P B ψ)) :=
    tendsto_const_nhds.congr' (Filter.eventually_atTop.2 ⟨2, fun N hN => (hev N hN).symm⟩)
  simpa using tendsto_nhds_unique h h2

lemma pvm_mul_of_disjoint (hP : IsProjValuedMeasure P) {A B : Set ℝ} (hA : MeasurableSet A)
    (hB : MeasurableSet B) (hAB : Disjoint A B) : P A * P B = 0 := by
  have hp := (hP.1 A hA).2
  have hq := (hP.1 B hB).2
  have hpq := (hP.1 (A ∪ B) (hA.union hB)).2
  rw [pvm_union hP hA hB hAB] at hpq
  set p := P A
  set q := P B
  have h1 : p * q + q * p = 0 := by
    have := hpq.eq
    simp only [add_mul, mul_add, hp.eq, hq.eq] at this
    have h' : p * q + q * p = (p + q * p + (p * q + q)) - (p + q) := by abel
    rw [h', this, sub_self]
  have h2 : p * q + p * q * p = 0 := by
    have := congrArg (fun x => p * x) h1
    simp only [mul_add, mul_zero, ← mul_assoc, hp.eq] at this
    exact this
  have h3 : p * q * p + q * p = 0 := by
    have := congrArg (fun x => x * p) h1
    simp only [add_mul, zero_mul, mul_assoc, hp.eq] at this
    simpa [mul_assoc] using this
  have h4 : p * q = q * p := by
    have e1 : p * q = - (p * q * p) := eq_neg_of_add_eq_zero_left h2
    have e2 : q * p = - (p * q * p) := eq_neg_of_add_eq_zero_right h3
    rw [e1, e2]
  have h5 : (2 : ℂ) • (p * q) = 0 := by
    rw [two_smul]; nth_rewrite 2 [h4]; exact h1
  rcases smul_eq_zero.1 h5 with h | h
  · norm_num at h
  · exact h

lemma pvm_inter (hP : IsProjValuedMeasure P) {A B : Set ℝ} (hA : MeasurableSet A)
    (hB : MeasurableSet B) : P (A ∩ B) = P A * P B := by
  have eA : A = (A ∩ B) ∪ (A \ B) := (Set.inter_union_diff A B).symm
  have eB : B = (A ∩ B) ∪ (B \ A) := by
    rw [Set.inter_comm]; exact (Set.inter_union_diff B A).symm
  have dA : Disjoint (A ∩ B) (A \ B) := Set.disjoint_sdiff_inter.symm
  have dB : Disjoint (A ∩ B) (B \ A) := by
    rw [Set.inter_comm]; exact Set.disjoint_sdiff_inter.symm
  have hI := hA.inter hB
  have hAB := hA.diff hB
  have hBA := hB.diff hA
  have hPA : P A = P (A ∩ B) + P (A \ B) := by
    conv_lhs => rw [eA]
    exact pvm_union hP hI hAB dA
  have hPB : P B = P (A ∩ B) + P (B \ A) := by
    conv_lhs => rw [eB]
    exact pvm_union hP hI hBA dB
  have z1 : P (A ∩ B) * P (B \ A) = 0 := pvm_mul_of_disjoint hP hI hBA dB
  have z2 : P (A \ B) * P (A ∩ B) = 0 := pvm_mul_of_disjoint hP hAB hI dA.symm
  have z3 : P (A \ B) * P (B \ A) = 0 := pvm_mul_of_disjoint hP hAB hBA
    (Set.disjoint_left.2 (fun x hx hx' => hx.2 hx'.1))
  rw [hPA, hPB, add_mul, mul_add, mul_add, z1, z2, z3, (hP.1 _ hI).2.eq]
  simp

lemma pvm_adjoint (hP : IsProjValuedMeasure P) {A : Set ℝ} (hA : MeasurableSet A) :
    ContinuousLinearMap.adjoint (P A) = P A := by
  rw [← ContinuousLinearMap.star_eq_adjoint]; exact (hP.1 A hA).1

lemma pvm_inner_self (hP : IsProjValuedMeasure P) {A : Set ℝ} (hA : MeasurableSet A) (ψ : H) :
    ⟪ψ, P A ψ⟫_ℂ = ((‖P A ψ‖ ^ 2 : ℝ) : ℂ) := by
  have : P A ψ = P A (P A ψ) := by
    rw [← ContinuousLinearMap.mul_apply, (hP.1 A hA).2.eq]
  rw [this, ← ContinuousLinearMap.adjoint_inner_left, pvm_adjoint hP hA, ← this,
    inner_self_eq_norm_sq_to_K]
  norm_cast

lemma pvm_inner_disjoint (hP : IsProjValuedMeasure P) {A B : Set ℝ} (hA : MeasurableSet A)
    (hB : MeasurableSet B) (hAB : Disjoint A B) (ψ : H) : ⟪P A ψ, P B ψ⟫_ℂ = 0 := by
  rw [← ContinuousLinearMap.adjoint_inner_right, pvm_adjoint hP hA,
    ← ContinuousLinearMap.mul_apply, pvm_mul_of_disjoint hP hA hB hAB]
  simp

/-! ### The spectral measures `μ_ψ` -/

lemma spectralMeasure_cond (hP : IsProjValuedMeasure P) (ψ : H) :
    ((‖P ∅ ψ‖₊ : ℝ≥0∞) ^ 2 = 0 ∧
      ∀ ⦃Ω : ℕ → Set ℝ⦄, (∀ n, MeasurableSet (Ω n)) → Pairwise (Function.onFun Disjoint Ω) →
        (‖P (⋃ n, Ω n) ψ‖₊ : ℝ≥0∞) ^ 2 = ∑' n, (‖P (Ω n) ψ‖₊ : ℝ≥0∞) ^ 2) := by
  refine ⟨by simp [pvm_empty hP], ?_⟩
  intro Ω hΩm hΩd
  have h := hP.2.2 Ω hΩm hΩd ψ
  have hpy : ∀ N, ‖∑ n ∈ Finset.range N, P (Ω n) ψ‖ ^ 2 =
      ∑ n ∈ Finset.range N, ‖P (Ω n) ψ‖ ^ 2 := by
    intro N
    induction N with
    | zero => simp
    | succ N ih =>
      rw [Finset.sum_range_succ, Finset.sum_range_succ, ← ih, sq, sq, sq]
      apply norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero (𝕜 := ℂ)
      rw [sum_inner (𝕜 := ℂ)]
      apply Finset.sum_eq_zero
      intro n hn
      exact pvm_inner_disjoint hP (hΩm n) (hΩm N)
        (hΩd (by simp at hn; omega)) ψ
  have h1 : Filter.Tendsto (fun N => ENNReal.ofReal (∑ n ∈ Finset.range N, ‖P (Ω n) ψ‖ ^ 2))
      Filter.atTop (nhds (ENNReal.ofReal (‖P (⋃ n, Ω n) ψ‖ ^ 2))) := by
    apply (ENNReal.continuous_ofReal.tendsto _).comp
    simp_rw [← hpy]
    exact ((continuous_pow 2).tendsto _).comp ((continuous_norm.tendsto _).comp h)
  have h2 : (fun N => ENNReal.ofReal (∑ n ∈ Finset.range N, ‖P (Ω n) ψ‖ ^ 2)) =
      fun N => ∑ n ∈ Finset.range N, (‖P (Ω n) ψ‖₊ : ℝ≥0∞) ^ 2 := by
    funext N
    rw [ENNReal.ofReal_sum_of_nonneg (fun _ _ => by positivity)]
    congr 1; funext n
    rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm_eq_enorm]
    rfl
  rw [h2] at h1
  have h3 := tendsto_nhds_unique h1 (ENNReal.tendsto_nat_tsum _)
  rw [← h3, ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm_eq_enorm]
  rfl

lemma spectralMeasure_apply (hP : IsProjValuedMeasure P) (ψ : H) {A : Set ℝ}
    (hA : MeasurableSet A) : spectralMeasure P ψ A = (‖P A ψ‖₊ : ℝ≥0∞) ^ 2 := by
  unfold spectralMeasure
  rw [dif_pos (spectralMeasure_cond hP ψ), Measure.ofMeasurable_apply _ hA]

lemma spectralMeasure_real (hP : IsProjValuedMeasure P) (ψ : H) {A : Set ℝ}
    (hA : MeasurableSet A) : (spectralMeasure P ψ).real A = ‖P A ψ‖ ^ 2 := by
  rw [measureReal_def, spectralMeasure_apply hP ψ hA]
  simp

lemma spectralMeasure_univ (hP : IsProjValuedMeasure P) (ψ : H) :
    (spectralMeasure P ψ).real Set.univ = ‖ψ‖ ^ 2 := by
  rw [spectralMeasure_real hP ψ MeasurableSet.univ, hP.2.1]
  simp

lemma spectralMeasure_finite (hP : IsProjValuedMeasure P) (ψ : H) :
    IsFiniteMeasure (spectralMeasure P ψ) := by
  constructor
  rw [spectralMeasure_apply hP ψ MeasurableSet.univ]
  exact ENNReal.pow_lt_top ENNReal.coe_lt_top


/-! ### Bounded Borel functions -/

lemma isBoundedBorel_indicator {A : Set ℝ} (hA : MeasurableSet A) :
    IsBoundedBorel (A.indicator (1 : ℝ → ℂ)) := by
  refine ⟨measurable_one.indicator hA, 1, fun x => ?_⟩
  by_cases hx : x ∈ A <;> simp [hx]

lemma isBoundedBorel_const (c : ℂ) : IsBoundedBorel (fun _ : ℝ => c) :=
  ⟨measurable_const, ‖c‖, fun _ => le_rfl⟩

lemma ibb_add {f g : ℝ → ℂ} (hf : IsBoundedBorel f) (hg : IsBoundedBorel g) :
    IsBoundedBorel (f + g) := by
  obtain ⟨C, hC⟩ := hf.2
  obtain ⟨D, hD⟩ := hg.2
  exact ⟨hf.1.add hg.1, C + D, fun x => (norm_add_le _ _).trans (add_le_add (hC x) (hD x))⟩

lemma ibb_mul {f g : ℝ → ℂ} (hf : IsBoundedBorel f) (hg : IsBoundedBorel g) :
    IsBoundedBorel (f * g) := by
  obtain ⟨C, hC⟩ := hf.2
  obtain ⟨D, hD⟩ := hg.2
  refine ⟨hf.1.mul hg.1, C * D, fun x => ?_⟩
  simp only [Pi.mul_apply, norm_mul]
  exact mul_le_mul (hC x) (hD x) (norm_nonneg _) ((norm_nonneg _).trans (hC x))

lemma ibb_smul {f : ℝ → ℂ} (c : ℂ) (hf : IsBoundedBorel f) :
    IsBoundedBorel (c • f) := by
  obtain ⟨C, hC⟩ := hf.2
  refine ⟨hf.1.const_smul c, ‖c‖ * C, fun x => ?_⟩
  simp only [Pi.smul_apply, smul_eq_mul, norm_mul]
  exact mul_le_mul_of_nonneg_left (hC x) (norm_nonneg _)

lemma ibb_neg {f : ℝ → ℂ} (hf : IsBoundedBorel f) : IsBoundedBorel (-f) := by
  have := ibb_smul (-1) hf
  simpa using this

lemma ibb_sub {f g : ℝ → ℂ} (hf : IsBoundedBorel f) (hg : IsBoundedBorel g) :
    IsBoundedBorel (f - g) := by
  rw [sub_eq_add_neg]; exact ibb_add hf (ibb_neg hg)

lemma ibb_star {f : ℝ → ℂ} (hf : IsBoundedBorel f) : IsBoundedBorel (star f) := by
  obtain ⟨C, hC⟩ := hf.2
  refine ⟨Complex.continuous_conj.measurable.comp hf.1, C, fun x => ?_⟩
  simpa using hC x

lemma ibb_integrable (hP : IsProjValuedMeasure P) {f : ℝ → ℂ} (hf : IsBoundedBorel f)
    (ψ : H) : Integrable f (spectralMeasure P ψ) := by
  haveI := spectralMeasure_finite hP ψ
  obtain ⟨C, hC⟩ := hf.2
  exact Integrable.of_bound hf.1.aestronglyMeasurable C (Filter.Eventually.of_forall hC)

lemma norm_integral_spectralMeasure_le (hP : IsProjValuedMeasure P) {f : ℝ → ℂ} {C : ℝ}
    (hC : ∀ x, ‖f x‖ ≤ C) (ψ : H) :
    ‖∫ x, f x ∂spectralMeasure P ψ‖ ≤ C * ‖ψ‖ ^ 2 := by
  haveI := spectralMeasure_finite hP ψ
  have := norm_integral_le_of_norm_le_const (μ := spectralMeasure P ψ)
    (Filter.Eventually.of_forall hC)
  rwa [spectralMeasure_univ hP] at this

/-! ### Operators representing a quadratic form -/

/-- `T` represents `f`: `⟨ψ, T ψ⟩ = ∫ f dμ_ψ` for all `ψ`. -/
def Rep (P : Set ℝ → (H →L[ℂ] H)) (f : ℝ → ℂ) (T : H →L[ℂ] H) : Prop :=
  ∀ ψ : H, ⟪ψ, T ψ⟫_ℂ = ∫ x, f x ∂spectralMeasure P ψ

lemma ext_of_inner_self {T S : H →L[ℂ] H} (h : ∀ ψ, ⟪ψ, T ψ⟫_ℂ = ⟪ψ, S ψ⟫_ℂ) : T = S := by
  have h0 : ((T - S : H →L[ℂ] H) : H →ₗ[ℂ] H) = 0 := by
    rw [← inner_map_self_eq_zero]
    intro x
    simp only [ContinuousLinearMap.coe_sub, LinearMap.sub_apply, ContinuousLinearMap.coe_coe,
      inner_sub_left]
    rw [← inner_conj_symm (T x) x, ← inner_conj_symm (S x) x, h x, sub_self]
  have h1 : T - S = 0 := by
    ext x
    have := LinearMap.congr_fun h0 x
    simpa using this
  exact sub_eq_zero.1 h1

lemma polarization (T : H →L[ℂ] H) (φ ψ : H) :
    ⟪φ, T ψ⟫_ℂ = (1/4 : ℂ) * (⟪φ + ψ, T (φ + ψ)⟫_ℂ - ⟪φ - ψ, T (φ - ψ)⟫_ℂ +
      Complex.I * ⟪φ - Complex.I • ψ, T (φ - Complex.I • ψ)⟫_ℂ -
      Complex.I * ⟪φ + Complex.I • ψ, T (φ + Complex.I • ψ)⟫_ℂ) := by
  simp only [map_add, map_sub, map_smul, inner_add_left, inner_add_right, inner_sub_left,
    inner_sub_right, inner_smul_left, inner_smul_right, Complex.conj_I]
  ring_nf
  simp only [Complex.I_sq]
  ring

lemma rep_unique {f : ℝ → ℂ} {T S : H →L[ℂ] H} (hT : Rep P f T) (hS : Rep P f S) : T = S :=
  ext_of_inner_self (fun ψ => by rw [hT ψ, hS ψ])

lemma rep_indicator (hP : IsProjValuedMeasure P) {A : Set ℝ} (hA : MeasurableSet A) :
    Rep P (A.indicator 1) (P A) := by
  intro ψ
  rw [pvm_inner_self hP hA, integral_indicator hA]
  simp only [Pi.one_apply]
  rw [setIntegral_const, spectralMeasure_real hP ψ hA]
  simp

lemma rep_add (hP : IsProjValuedMeasure P) {f g : ℝ → ℂ} {T S : H →L[ℂ] H}
    (hf : IsBoundedBorel f) (hg : IsBoundedBorel g) (hT : Rep P f T) (hS : Rep P g S) :
    Rep P (f + g) (T + S) := by
  intro ψ
  rw [ContinuousLinearMap.add_apply, inner_add_right, hT ψ, hS ψ,
    ← integral_add (ibb_integrable hP hf ψ) (ibb_integrable hP hg ψ)]
  rfl

lemma rep_smul {f : ℝ → ℂ} {T : H →L[ℂ] H} (c : ℂ) (hT : Rep P f T) :
    Rep P (c • f) (c • T) := by
  intro ψ
  rw [ContinuousLinearMap.smul_apply, inner_smul_right, hT ψ, Pi.smul_def]
  simp only [smul_eq_mul]
  rw [integral_const_mul]

lemma rep_sub (hP : IsProjValuedMeasure P) {f g : ℝ → ℂ} {T S : H →L[ℂ] H}
    (hf : IsBoundedBorel f) (hg : IsBoundedBorel g) (hT : Rep P f T) (hS : Rep P g S) :
    Rep P (f - g) (T - S) := by
  have := rep_add hP hf (ibb_smul (-1) hg) hT (rep_smul (-1) hS)
  simpa [sub_eq_add_neg] using this

lemma rep_star {f : ℝ → ℂ} {T : H →L[ℂ] H} (hT : Rep P f T) :
    Rep P (star f) (ContinuousLinearMap.adjoint T) := by
  intro ψ
  rw [ContinuousLinearMap.adjoint_inner_right, ← inner_conj_symm, hT ψ, ← integral_conj]
  rfl

lemma opNorm_le_of_inner_self (T : H →L[ℂ] H) {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ ψ, ‖⟪ψ, T ψ⟫_ℂ‖ ≤ C * ‖ψ‖ ^ 2) : ‖T‖ ≤ 2 * C := by
  have key : ∀ φ ψ : H, ‖⟪φ, T ψ⟫_ℂ‖ ≤ C * (‖φ‖ ^ 2 + ‖ψ‖ ^ 2) := by
    intro φ ψ
    rw [polarization T φ ψ]
    have p1 := parallelogram_law_with_norm ℂ φ ψ
    have p2 := parallelogram_law_with_norm ℂ φ (Complex.I • ψ)
    have nI : ‖Complex.I • ψ‖ = ‖ψ‖ := by simp [norm_smul]
    rw [nI] at p2
    have e1 := h (φ + ψ)
    have e2 := h (φ - ψ)
    have e3 := h (φ - Complex.I • ψ)
    have e4 := h (φ + Complex.I • ψ)
    calc _ = (1/4 : ℝ) * ‖⟪φ + ψ, T (φ + ψ)⟫_ℂ - ⟪φ - ψ, T (φ - ψ)⟫_ℂ +
          Complex.I * ⟪φ - Complex.I • ψ, T (φ - Complex.I • ψ)⟫_ℂ -
          Complex.I * ⟪φ + Complex.I • ψ, T (φ + Complex.I • ψ)⟫_ℂ‖ := by
            rw [norm_mul]; norm_num
      _ ≤ (1/4 : ℝ) * (‖⟪φ + ψ, T (φ + ψ)⟫_ℂ‖ + ‖⟪φ - ψ, T (φ - ψ)⟫_ℂ‖ +
          ‖⟪φ - Complex.I • ψ, T (φ - Complex.I • ψ)⟫_ℂ‖ +
          ‖⟪φ + Complex.I • ψ, T (φ + Complex.I • ψ)⟫_ℂ‖) := by
            gcongr
            refine (norm_sub_le _ _).trans ?_
            refine add_le_add ((norm_add_le _ _).trans (add_le_add (norm_sub_le _ _) ?_)) ?_
            · simp
            · simp
      _ ≤ (1/4 : ℝ) * (C * ‖φ + ψ‖ ^ 2 + C * ‖φ - ψ‖ ^ 2 + C * ‖φ - Complex.I • ψ‖ ^ 2 +
          C * ‖φ + Complex.I • ψ‖ ^ 2) := by gcongr
      _ = C * (‖φ‖ ^ 2 + ‖ψ‖ ^ 2) := by
            have : ‖φ + Complex.I • ψ‖ ^ 2 + ‖φ - Complex.I • ψ‖ ^ 2 = 2 * (‖φ‖ ^ 2 + ‖ψ‖ ^ 2) := by
              nlinarith [p2]
            have : ‖φ + ψ‖ ^ 2 + ‖φ - ψ‖ ^ 2 = 2 * (‖φ‖ ^ 2 + ‖ψ‖ ^ 2) := by
              nlinarith [p1]
            nlinarith
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro ψ
  by_cases hψ : T ψ = 0
  · rw [hψ, norm_zero]; positivity
  have ha : 0 < ‖T ψ‖ := norm_pos_iff.2 hψ
  have hb : 0 < ‖ψ‖ := by
    rcases (norm_nonneg ψ).lt_or_eq with h' | h'
    · exact h'
    · exfalso; apply hψ; rw [norm_eq_zero.1 h'.symm, map_zero]
  have k := key (((‖ψ‖ / ‖T ψ‖ : ℝ) : ℂ) • T ψ) ψ
  rw [inner_smul_left, inner_self_eq_norm_sq_to_K, norm_smul] at k
  simp only [Complex.conj_ofReal, norm_mul, Complex.norm_real, Real.norm_eq_abs, norm_pow,
    abs_div, abs_norm] at k
  have e : ‖ψ‖ / ‖T ψ‖ * ‖T ψ‖ = ‖ψ‖ := div_mul_cancel₀ _ ha.ne'
  rw [e] at k
  rw [RCLike.norm_ofReal, abs_norm] at k
  have e2 : ‖ψ‖ / ‖T ψ‖ * ‖T ψ‖ ^ 2 = ‖ψ‖ * ‖T ψ‖ := by
    field_simp
  rw [e2] at k
  nlinarith

lemma rep_norm_le (hP : IsProjValuedMeasure P) {f : ℝ → ℂ} {T : H →L[ℂ] H} {C : ℝ}
    (hC : ∀ x, ‖f x‖ ≤ C) (hT : Rep P f T) : ‖T‖ ≤ 2 * C := by
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 0)
  apply opNorm_le_of_inner_self T hC0
  intro ψ
  rw [hT ψ]
  exact norm_integral_spectralMeasure_le hP hC ψ

/-! ### Uniform limits -/

lemma rep_limit (hP : IsProjValuedMeasure P) {fs : ℕ → ℝ → ℂ} {f : ℝ → ℂ}
    {T : ℕ → H →L[ℂ] H} (hfs : ∀ n, IsBoundedBorel (fs n)) (hf : IsBoundedBorel f)
    (hT : ∀ n, Rep P (fs n) (T n)) (hu : TendstoUniformly fs f Filter.atTop) :
    ∃ S, Rep P f S ∧ Filter.Tendsto T Filter.atTop (nhds S) := by
  have hcauchy : CauchySeq T := by
    rw [Metric.cauchySeq_iff]
    intro ε hε
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.1
      ((Metric.tendstoUniformly_iff.1 hu) (ε / 8) (by positivity))
    refine ⟨N, fun m hm n hn => ?_⟩
    rw [dist_eq_norm]
    have hb : ∀ x, ‖(fs m - fs n) x‖ ≤ ε / 4 := by
      intro x
      have h1 := hN m hm x
      have h2 := hN n hn x
      rw [dist_eq_norm] at h1 h2
      calc ‖(fs m - fs n) x‖ = ‖(f x - fs n x) - (f x - fs m x)‖ := by
            simp only [Pi.sub_apply]; congr 1; abel
        _ ≤ ‖f x - fs n x‖ + ‖f x - fs m x‖ := norm_sub_le _ _
        _ ≤ ε / 4 := by linarith
    have := rep_norm_le hP hb (rep_sub hP (hfs m) (hfs n) (hT m) (hT n))
    linarith
  obtain ⟨S, hS⟩ := cauchySeq_tendsto_of_complete hcauchy
  refine ⟨S, fun ψ => ?_, hS⟩
  have h1 : Filter.Tendsto (fun n => ⟪ψ, T n ψ⟫_ℂ) Filter.atTop (nhds ⟪ψ, S ψ⟫_ℂ) := by
    have : Filter.Tendsto (fun n => T n ψ) Filter.atTop (nhds (S ψ)) :=
      ((ContinuousLinearMap.apply ℂ H ψ).continuous.tendsto S).comp hS
    exact Filter.Tendsto.inner tendsto_const_nhds this
  have h2 : Filter.Tendsto (fun n => ⟪ψ, T n ψ⟫_ℂ) Filter.atTop
      (nhds (∫ x, f x ∂spectralMeasure P ψ)) := by
    have hT' : ∀ n, ⟪ψ, T n ψ⟫_ℂ = ∫ x, fs n x ∂spectralMeasure P ψ := fun n => hT n ψ
    simp_rw [hT']
    rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 ((Metric.tendstoUniformly_iff.1 hu)
      (ε / (2 * (‖ψ‖ ^ 2 + 1))) (by positivity))
    refine ⟨N, fun n hn => ?_⟩
    rw [dist_eq_norm, ← integral_sub (ibb_integrable hP (hfs n) ψ) (ibb_integrable hP hf ψ)]
    have hb : ∀ x, ‖fs n x - f x‖ ≤ ε / (2 * (‖ψ‖ ^ 2 + 1)) := by
      intro x; have := hN n hn x; rw [dist_comm, dist_eq_norm] at this; exact this.le
    have := norm_integral_spectralMeasure_le hP hb ψ
    calc _ ≤ _ := this
      _ < ε := by
        rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
        nlinarith [sq_nonneg ‖ψ‖]
  exact tendsto_nhds_unique h1 h2

lemma ibb_finset_sum {ι : Type*} (s : Finset ι) (c : ι → ℂ) (A : ι → Set ℝ)
    (hA : ∀ i, MeasurableSet (A i)) :
    IsBoundedBorel (∑ i ∈ s, c i • (A i).indicator (1 : ℝ → ℂ)) := by
  induction s using Finset.cons_induction with
  | empty => rw [Finset.sum_empty]; exact isBoundedBorel_const 0
  | cons a s ha ih =>
    rw [Finset.sum_cons]
    exact ibb_add (ibb_smul _ (isBoundedBorel_indicator (hA a))) ih

/-- Induction principle for bounded Borel functions: a property that holds for indicators of
Borel sets and is stable under linear combinations and uniform limits holds for all bounded
Borel functions. -/
lemma isBoundedBorel_induction (Q : (ℝ → ℂ) → Prop)
    (hind : ∀ A, MeasurableSet A → Q (A.indicator 1))
    (hadd : ∀ f g, IsBoundedBorel f → IsBoundedBorel g → Q f → Q g → Q (f + g))
    (hsmul : ∀ (c : ℂ) f, IsBoundedBorel f → Q f → Q (c • f))
    (hlim : ∀ (fs : ℕ → ℝ → ℂ) (f : ℝ → ℂ), (∀ n, IsBoundedBorel (fs n)) → (∀ n, Q (fs n)) →
      IsBoundedBorel f → TendstoUniformly fs f Filter.atTop → Q f) :
    ∀ f, IsBoundedBorel f → Q f := by
  have hsum : ∀ (s : Finset ℤ) (c : ℤ → ℂ) (A : ℤ → Set ℝ), (∀ i, MeasurableSet (A i)) →
      Q (∑ i ∈ s, c i • (A i).indicator 1) := by
    intro s c A hA
    induction s using Finset.cons_induction with
    | empty =>
      rw [Finset.sum_empty]
      convert hind ∅ MeasurableSet.empty using 1
      ext x; simp
    | cons a s ha ih =>
      rw [Finset.sum_cons]
      exact hadd _ _ (ibb_smul _ (isBoundedBorel_indicator (hA a))) (ibb_finset_sum s c A hA)
        (hsmul _ _ (isBoundedBorel_indicator (hA a)) (hind _ (hA a))) ih
  have hreal : ∀ g : ℝ → ℝ, Measurable g → (∃ C, ∀ x, |g x| ≤ C) →
      Q (fun x => (g x : ℂ)) := by
    rintro g hg ⟨C, hC⟩
    let M : ℕ → ℤ := fun n => ⌈((n:ℝ) + 1) * C⌉ + 1
    let A : ℕ → ℤ → Set ℝ := fun n j => {x | ⌊((n:ℝ) + 1) * g x⌋ = j}
    have hA : ∀ n j, MeasurableSet (A n j) := fun n j =>
      (Int.measurable_floor.comp (measurable_const.mul hg)) (measurableSet_singleton j)
    let fs : ℕ → ℝ → ℂ := fun n => ∑ j ∈ Finset.Icc (-M n) (M n),
      (((j : ℝ) / ((n : ℝ) + 1) : ℝ) : ℂ) • (A n j).indicator 1
    have hfs_eval : ∀ n x, fs n x = (((⌊((n:ℝ) + 1) * g x⌋ : ℝ) / ((n : ℝ) + 1) : ℝ) : ℂ) := by
      intro n x
      simp only [fs, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      rw [Finset.sum_eq_single_of_mem ⌊((n:ℝ) + 1) * g x⌋]
      · simp [A]
      · rw [Finset.mem_Icc]
        have hn : (0:ℝ) < (n:ℝ) + 1 := by positivity
        have u1 : ((n:ℝ) + 1) * g x ≤ ((n:ℝ) + 1) * C :=
          mul_le_mul_of_nonneg_left ((le_abs_self _).trans (hC x)) hn.le
        have u2 : -(((n:ℝ) + 1) * C) ≤ ((n:ℝ) + 1) * g x := by
          have := neg_abs_le (g x)
          have := hC x
          nlinarith
        have f1 := Int.floor_le (((n:ℝ) + 1) * g x)
        have f2 := Int.sub_one_lt_floor (((n:ℝ) + 1) * g x)
        have c1 := Int.le_ceil (((n:ℝ) + 1) * C)
        have i1 : ((⌊((n:ℝ) + 1) * g x⌋ : ℤ) : ℝ) < ((⌈((n:ℝ) + 1) * C⌉ + 1 : ℤ) : ℝ) := by
          push_cast; linarith
        have i2 : ((-⌈((n:ℝ) + 1) * C⌉ - 2 : ℤ) : ℝ) < ((⌊((n:ℝ) + 1) * g x⌋ : ℤ) : ℝ) := by
          push_cast; linarith
        have j1 := Int.cast_lt.1 i1
        have j2 := Int.cast_lt.1 i2
        simp only [M]
        constructor <;> omega
      · intro j _ hj
        have : x ∉ A n j := by simp only [A, Set.mem_setOf_eq]; exact fun h => hj h.symm
        simp [this]
    have hfsQ : ∀ n, Q (fs n) := fun n => hsum _ _ _ (hA n)
    have hfsB : ∀ n, IsBoundedBorel (fs n) := fun n => ibb_finset_sum _ _ _ (hA n)
    have hgB : IsBoundedBorel (fun x => (g x : ℂ)) :=
      ⟨Complex.measurable_ofReal.comp hg, C, fun x => by simpa [Complex.norm_real] using hC x⟩
    apply hlim fs _ hfsB hfsQ hgB
    rw [Metric.tendstoUniformly_iff]
    intro ε hε
    obtain ⟨N, hN⟩ := exists_nat_one_div_lt hε
    filter_upwards [Filter.eventually_ge_atTop N] with n hn x
    rw [hfs_eval, Complex.dist_eq, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    have hn' : (0:ℝ) < n + 1 := by positivity
    have f1 := Int.floor_le (((n:ℝ) + 1) * g x)
    have f2 := Int.lt_floor_add_one (((n:ℝ) + 1) * g x)
    have e : g x - (⌊((n:ℝ) + 1) * g x⌋ : ℝ) / ((n:ℝ) + 1) =
        (((n:ℝ) + 1) * g x - ⌊((n:ℝ) + 1) * g x⌋) / ((n:ℝ) + 1) := by
      field_simp
    rw [e, abs_of_nonneg (div_nonneg (by linarith) hn'.le), div_lt_iff₀ hn']
    have h1 : 1 < ε * ((N:ℝ) + 1) := by
      rw [div_lt_iff₀ (by positivity)] at hN; linarith
    have h2 : (N:ℝ) ≤ n := by exact_mod_cast hn
    nlinarith
  intro f hf
  obtain ⟨C, hC⟩ := hf.2
  have hre : Q (fun x => ((f x).re : ℂ)) := hreal _ (Complex.measurable_re.comp hf.1)
    ⟨C, fun x => (Complex.abs_re_le_norm _).trans (hC x)⟩
  have him : Q (fun x => ((f x).im : ℂ)) := hreal _ (Complex.measurable_im.comp hf.1)
    ⟨C, fun x => (Complex.abs_im_le_norm _).trans (hC x)⟩
  have ibre : IsBoundedBorel (fun x => ((f x).re : ℂ)) :=
    ⟨Complex.measurable_ofReal.comp (Complex.measurable_re.comp hf.1), C,
      fun x => by simpa [Complex.norm_real] using (Complex.abs_re_le_norm _).trans (hC x)⟩
  have ibim : IsBoundedBorel (fun x => ((f x).im : ℂ)) :=
    ⟨Complex.measurable_ofReal.comp (Complex.measurable_im.comp hf.1), C,
      fun x => by simpa [Complex.norm_real] using (Complex.abs_im_le_norm _).trans (hC x)⟩
  have := hadd _ _ ibre (ibb_smul Complex.I ibim) hre (hsmul _ _ ibim him)
  convert this using 1
  funext x
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [mul_comm]
  exact (Complex.re_add_im _).symm

/-! ### Existence of `P(f)` and its algebraic properties -/

lemma exists_rep (hP : IsProjValuedMeasure P) {f : ℝ → ℂ} (hf : IsBoundedBorel f) :
    ∃ T, Rep P f T := by
  refine isBoundedBorel_induction (fun f => ∃ T, Rep P f T) ?_ ?_ ?_ ?_ f hf
  · intro A hA; exact ⟨P A, rep_indicator hP hA⟩
  · rintro f g hf hg ⟨T, hT⟩ ⟨S, hS⟩; exact ⟨T + S, rep_add hP hf hg hT hS⟩
  · rintro c f - ⟨T, hT⟩; exact ⟨c • T, rep_smul c hT⟩
  · intro fs f hfs hQ hf hu
    choose T hT using hQ
    obtain ⟨S, hS, -⟩ := rep_limit hP hfs hf hT hu
    exact ⟨S, hS⟩

lemma rep_bsi (hP : IsProjValuedMeasure P) {f : ℝ → ℂ} (hf : IsBoundedBorel f) :
    Rep P f (boundedSpectralIntegral P f) := by
  have h := exists_rep hP hf
  have h' : ∃ T : H →L[ℂ] H, ∀ ψ : H, ⟪ψ, T ψ⟫_ℂ = ∫ x, f x ∂spectralMeasure P ψ := h
  unfold boundedSpectralIntegral
  rw [dif_pos h']
  exact h'.choose_spec

lemma bsi_eq (hP : IsProjValuedMeasure P) {f : ℝ → ℂ} (hf : IsBoundedBorel f) {T : H →L[ℂ] H}
    (hT : Rep P f T) : boundedSpectralIntegral P f = T :=
  rep_unique (rep_bsi hP hf) hT

lemma bsi_add (hP : IsProjValuedMeasure P) {f g : ℝ → ℂ} (hf : IsBoundedBorel f)
    (hg : IsBoundedBorel g) :
    boundedSpectralIntegral P (f + g) =
      boundedSpectralIntegral P f + boundedSpectralIntegral P g :=
  bsi_eq hP (ibb_add hf hg) (rep_add hP hf hg (rep_bsi hP hf) (rep_bsi hP hg))

lemma bsi_sub (hP : IsProjValuedMeasure P) {f g : ℝ → ℂ} (hf : IsBoundedBorel f)
    (hg : IsBoundedBorel g) :
    boundedSpectralIntegral P (f - g) =
      boundedSpectralIntegral P f - boundedSpectralIntegral P g :=
  bsi_eq hP (ibb_sub hf hg) (rep_sub hP hf hg (rep_bsi hP hf) (rep_bsi hP hg))

lemma bsi_smul (hP : IsProjValuedMeasure P) (c : ℂ) {f : ℝ → ℂ} (hf : IsBoundedBorel f) :
    boundedSpectralIntegral P (c • f) = c • boundedSpectralIntegral P f :=
  bsi_eq hP (ibb_smul c hf) (rep_smul c (rep_bsi hP hf))

lemma bsi_indicator (hP : IsProjValuedMeasure P) {A : Set ℝ} (hA : MeasurableSet A) :
    boundedSpectralIntegral P (A.indicator 1) = P A :=
  bsi_eq hP (isBoundedBorel_indicator hA) (rep_indicator hP hA)

lemma bsi_star (hP : IsProjValuedMeasure P) {f : ℝ → ℂ} (hf : IsBoundedBorel f) :
    boundedSpectralIntegral P (star f) =
      ContinuousLinearMap.adjoint (boundedSpectralIntegral P f) :=
  bsi_eq hP (ibb_star hf) (rep_star (rep_bsi hP hf))

lemma bsi_tendsto (hP : IsProjValuedMeasure P) {fs : ℕ → ℝ → ℂ} {f : ℝ → ℂ}
    (hfs : ∀ n, IsBoundedBorel (fs n)) (hf : IsBoundedBorel f)
    (hu : TendstoUniformly fs f Filter.atTop) :
    Filter.Tendsto (fun n => boundedSpectralIntegral P (fs n)) Filter.atTop
      (nhds (boundedSpectralIntegral P f)) := by
  obtain ⟨S, hS, hT⟩ := rep_limit hP hfs hf (fun n => rep_bsi hP (hfs n)) hu
  rwa [bsi_eq hP hf hS]

lemma tendstoUniformly_mul_left {fs : ℕ → ℝ → ℂ} {f g : ℝ → ℂ}
    (hu : TendstoUniformly fs f Filter.atTop) (hg : ∃ C, ∀ x, ‖g x‖ ≤ C) :
    TendstoUniformly (fun n => g * fs n) (g * f) Filter.atTop := by
  obtain ⟨C, hC⟩ := hg
  rw [Metric.tendstoUniformly_iff] at hu ⊢
  intro ε hε
  have hC' : 0 < C + 1 := by linarith [(norm_nonneg _).trans (hC 0)]
  filter_upwards [hu (ε / (C + 1)) (by positivity)] with n hn x
  simp only [dist_eq_norm] at hn ⊢
  simp only [Pi.mul_apply, ← mul_sub, norm_mul]
  calc ‖g x‖ * ‖f x - fs n x‖ ≤ (C + 1) * ‖f x - fs n x‖ := by
        gcongr; linarith [hC x]
    _ < (C + 1) * (ε / (C + 1)) := by gcongr; exact hn x
    _ = ε := by field_simp

lemma tendstoUniformly_mul_right {fs : ℕ → ℝ → ℂ} {f g : ℝ → ℂ}
    (hu : TendstoUniformly fs f Filter.atTop) (hg : ∃ C, ∀ x, ‖g x‖ ≤ C) :
    TendstoUniformly (fun n => fs n * g) (f * g) Filter.atTop := by
  have := tendstoUniformly_mul_left hu hg
  simp only [mul_comm g] at this
  exact this

lemma bsi_mul_indicator (hP : IsProjValuedMeasure P) {B : Set ℝ} (hB : MeasurableSet B)
    {f : ℝ → ℂ} (hf : IsBoundedBorel f) :
    boundedSpectralIntegral P (f * B.indicator 1) = boundedSpectralIntegral P f * P B := by
  refine isBoundedBorel_induction
    (fun f => boundedSpectralIntegral P (f * B.indicator 1) = boundedSpectralIntegral P f * P B)
    ?_ ?_ ?_ ?_ f hf
  · intro A hA
    have e : A.indicator (1 : ℝ → ℂ) * B.indicator 1 = (A ∩ B).indicator 1 := by
      funext x; by_cases ha : x ∈ A <;> by_cases hb : x ∈ B <;> simp [ha, hb]
    rw [e, bsi_indicator hP (hA.inter hB), bsi_indicator hP hA, pvm_inter hP hA hB]
  · intro f g hf hg h1 h2
    try simp only at h1 h2 ⊢
    rw [add_mul, bsi_add hP (ibb_mul hf (isBoundedBorel_indicator hB))
      (ibb_mul hg (isBoundedBorel_indicator hB)), h1, h2, bsi_add hP hf hg, add_mul]
  · intro c f hf h1
    try simp only at h1 ⊢
    rw [smul_mul_assoc, bsi_smul hP c (ibb_mul hf (isBoundedBorel_indicator hB)), h1,
      bsi_smul hP c hf, smul_mul_assoc]
  · intro fs f hfs hQ hf hu
    try simp only at hQ ⊢
    have t1 := bsi_tendsto hP (P := P) (fun n => ibb_mul (hfs n) (isBoundedBorel_indicator hB))
      (ibb_mul hf (isBoundedBorel_indicator hB))
      (tendstoUniformly_mul_right hu (isBoundedBorel_indicator hB).2)
    have t2 := (bsi_tendsto hP hfs hf hu).mul_const (P B)
    simp_rw [hQ] at t1
    exact tendsto_nhds_unique t1 t2

lemma bsi_mul (hP : IsProjValuedMeasure P) {f g : ℝ → ℂ} (hf : IsBoundedBorel f)
    (hg : IsBoundedBorel g) :
    boundedSpectralIntegral P (f * g) =
      boundedSpectralIntegral P f * boundedSpectralIntegral P g := by
  refine isBoundedBorel_induction
    (fun g => boundedSpectralIntegral P (f * g) =
      boundedSpectralIntegral P f * boundedSpectralIntegral P g) ?_ ?_ ?_ ?_ g hg
  · intro B hB
    rw [bsi_mul_indicator hP hB hf, bsi_indicator hP hB]
  · intro g1 g2 h1 h2 e1 e2
    try simp only at e1 e2 ⊢
    rw [mul_add, bsi_add hP (ibb_mul hf h1) (ibb_mul hf h2), e1, e2, bsi_add hP h1 h2, mul_add]
  · intro c g h1 e1
    try simp only at e1 ⊢
    rw [mul_smul_comm, bsi_smul hP c (ibb_mul hf h1), e1, bsi_smul hP c h1, mul_smul_comm]
  · intro gs g hgs hQ hg hu
    try simp only at hQ ⊢
    have t1 := bsi_tendsto hP (P := P) (fun n => ibb_mul hf (hgs n)) (ibb_mul hf hg)
      (tendstoUniformly_mul_left hu hf.2)
    have t2 := (bsi_tendsto hP hgs hg hu).const_mul (boundedSpectralIntegral P f)
    simp_rw [hQ] at t1
    exact tendsto_nhds_unique t1 t2

lemma bsi_norm_sq (hP : IsProjValuedMeasure P) {f : ℝ → ℂ} (hf : IsBoundedBorel f) (ψ : H) :
    ‖boundedSpectralIntegral P f ψ‖ ^ 2 = ∫ x, ‖f x‖ ^ 2 ∂spectralMeasure P ψ := by
  have h1 : ⟪boundedSpectralIntegral P f ψ, boundedSpectralIntegral P f ψ⟫_ℂ =
      ⟪ψ, boundedSpectralIntegral P (star f * f) ψ⟫_ℂ := by
    rw [bsi_mul hP (ibb_star hf) hf, bsi_star hP hf, ContinuousLinearMap.mul_apply,
      ContinuousLinearMap.adjoint_inner_right]
  rw [rep_bsi hP (ibb_mul (ibb_star hf) hf), inner_self_eq_norm_sq_to_K] at h1
  have h2 : (star f * f) = fun x => ((‖f x‖ ^ 2 : ℝ) : ℂ) := by
    funext x
    simp only [Pi.mul_apply, Pi.star_apply]
    rw [Complex.star_def, Complex.conj_mul']
    push_cast; rfl
  rw [h2] at h1
  simp only [integral_complex_ofReal] at h1
  exact Complex.ofReal_injective (by rw [Complex.ofReal_pow]; exact h1)

end TeschlQM.Spectral.BFC

namespace TeschlQM.Spectral

open TeschlQM.Spectral.BFC

/-- Teschl, p. 90, Theorem 3.1. -/
theorem bounded_functional_calculus {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (P : Set ℝ → (H →L[ℂ] H)) (hP : TeschlQM.Shared.IsProjValuedMeasure P) :
    boundedSpectralIntegral P 1 = 1 ∧
    (∀ f g : ℝ → ℂ, IsBoundedBorel f → IsBoundedBorel g →
      boundedSpectralIntegral P (f + g) =
          boundedSpectralIntegral P f + boundedSpectralIntegral P g ∧
      boundedSpectralIntegral P (f * g) =
          boundedSpectralIntegral P f * boundedSpectralIntegral P g) ∧
    (∀ (c : ℂ) (f : ℝ → ℂ), IsBoundedBorel f →
      boundedSpectralIntegral P (c • f) = c • boundedSpectralIntegral P f) ∧
    (∀ f : ℝ → ℂ, IsBoundedBorel f →
      boundedSpectralIntegral P (star f) = star (boundedSpectralIntegral P f)) ∧
    (∀ f : ℝ → ℂ, IsBoundedBorel f → ‖boundedSpectralIntegral P f‖ ≤ ⨆ x, ‖f x‖) ∧
    (∀ f g : ℝ → ℂ, IsBoundedBorel f → IsBoundedBorel g → ∀ φ ψ : H,
      ⟪boundedSpectralIntegral P g φ, boundedSpectralIntegral P f ψ⟫_ℂ =
        spectralForm P φ ψ (star g * f)) ∧
    (∀ (fs : ℕ → ℝ → ℂ) (f : ℝ → ℂ), (∀ n, IsBoundedBorel (fs n)) →
      (∀ x, Filter.Tendsto (fun n => fs n x) Filter.atTop (nhds (f x))) →
      (∃ C : ℝ, ∀ n x, ‖fs n x‖ ≤ C) →
      ∀ ψ : H, Filter.Tendsto (fun n => boundedSpectralIntegral P (fs n) ψ) Filter.atTop
        (nhds (boundedSpectralIntegral P f ψ))) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · apply bsi_eq hP (isBoundedBorel_const 1)
    intro ψ
    rw [ContinuousLinearMap.one_apply, inner_self_eq_norm_sq_to_K, integral_const,
      spectralMeasure_univ hP]
    simp
  · intro f g hf hg
    exact ⟨bsi_add hP hf hg, bsi_mul hP hf hg⟩
  · intro c f hf
    exact bsi_smul hP c hf
  · intro f hf
    rw [bsi_star hP hf, ContinuousLinearMap.star_eq_adjoint]
  · intro f hf
    have bdd : BddAbove (Set.range fun x => ‖f x‖) := by
      obtain ⟨C, hC⟩ := hf.2
      exact ⟨C, by rintro _ ⟨x, rfl⟩; exact hC x⟩
    have hle : ∀ x, ‖f x‖ ≤ ⨆ x, ‖f x‖ := fun x => le_ciSup bdd x
    have h0 : 0 ≤ ⨆ x, ‖f x‖ := (norm_nonneg _).trans (hle 0)
    apply ContinuousLinearMap.opNorm_le_bound _ h0
    intro ψ
    haveI := spectralMeasure_finite hP ψ
    have h1 := bsi_norm_sq hP hf ψ
    have h2 : ∫ x, ‖f x‖ ^ 2 ∂spectralMeasure P ψ ≤ (⨆ x, ‖f x‖) ^ 2 * ‖ψ‖ ^ 2 := by
      calc ∫ x, ‖f x‖ ^ 2 ∂spectralMeasure P ψ
          ≤ ∫ _x, (⨆ x, ‖f x‖) ^ 2 ∂spectralMeasure P ψ := by
            apply integral_mono_of_nonneg (Filter.Eventually.of_forall (fun x => by positivity))
              (integrable_const _)
            exact Filter.Eventually.of_forall (fun x =>
              pow_le_pow_left₀ (norm_nonneg _) (hle x) 2)
        _ = (⨆ x, ‖f x‖) ^ 2 * ‖ψ‖ ^ 2 := by
            rw [integral_const, smul_eq_mul, spectralMeasure_univ hP, mul_comm]
    have h3 : ‖boundedSpectralIntegral P f ψ‖ ^ 2 ≤ ((⨆ x, ‖f x‖) * ‖ψ‖) ^ 2 := by
      rw [h1, mul_pow]; exact h2
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 h3
  · intro f g hf hg φ ψ
    have h1 : ⟪boundedSpectralIntegral P g φ, boundedSpectralIntegral P f ψ⟫_ℂ =
        ⟪φ, boundedSpectralIntegral P (star g * f) ψ⟫_ℂ := by
      rw [bsi_mul hP (ibb_star hg) hf, bsi_star hP hg, ContinuousLinearMap.mul_apply,
        ContinuousLinearMap.adjoint_inner_right]
    rw [h1]
    have hr := rep_bsi hP (ibb_mul (ibb_star hg) hf)
    unfold spectralForm
    rw [← hr, ← hr, ← hr, ← hr]
    exact polarization _ φ ψ
  · intro fs f hfs hconv hbd ψ
    obtain ⟨C, hC⟩ := hbd
    have hfm : Measurable f :=
      measurable_of_tendsto_metrizable (fun n => (hfs n).1) (tendsto_pi_nhds.2 hconv)
    have hfC : ∀ x, ‖f x‖ ≤ C := fun x =>
      le_of_tendsto' ((continuous_norm.tendsto _).comp (hconv x)) (fun n => hC n x)
    have hf : IsBoundedBorel f := ⟨hfm, C, hfC⟩
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have e : ∀ n, ‖boundedSpectralIntegral P (fs n) ψ - boundedSpectralIntegral P f ψ‖ =
        Real.sqrt (∫ x, ‖fs n x - f x‖ ^ 2 ∂spectralMeasure P ψ) := by
      intro n
      rw [← ContinuousLinearMap.sub_apply, ← bsi_sub hP (hfs n) hf]
      have := bsi_norm_sq hP (ibb_sub (hfs n) hf) ψ
      simp only [Pi.sub_apply] at this
      rw [← this, Real.sqrt_sq (norm_nonneg _)]
    simp_rw [e]
    rw [← Real.sqrt_zero]
    apply (Real.continuous_sqrt.tendsto 0).comp
    haveI := spectralMeasure_finite hP ψ
    have := tendsto_integral_of_dominated_convergence (μ := spectralMeasure P ψ)
      (F := fun n x => ‖fs n x - f x‖ ^ 2) (f := fun _ => 0) (fun _ => (2 * C) ^ 2)
      (fun n => (((hfs n).1.sub hfm).norm.pow_const 2).aestronglyMeasurable)
      (integrable_const _)
      (fun n => Filter.Eventually.of_forall (fun x => by
        rw [Real.norm_of_nonneg (by positivity)]
        exact pow_le_pow_left₀ (norm_nonneg _)
          (by linarith [norm_sub_le (fs n x) (f x), hC n x, hfC x]) 2))
      (Filter.Eventually.of_forall (fun x => by
        have := (((hconv x).sub_const (f x)).norm).pow 2
        simpa using this))
    simpa using this

end TeschlQM.Spectral


open MeasureTheory
open scoped ENNReal InnerProductSpace

namespace TeschlQM.Spectral.BFC

open TeschlQM.Shared TeschlQM.Spectral

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {P : Set ℝ → (H →L[ℂ] H)}

/-! ### Spectral measures of transformed vectors -/

lemma spectralMeasure_smul (hP : IsProjValuedMeasure P) (c : ℂ) (ψ : H) :
    spectralMeasure P (c • ψ) = ((‖c‖₊ : ℝ≥0∞) ^ 2) • spectralMeasure P ψ := by
  ext Ω hΩ
  rw [Measure.smul_apply, spectralMeasure_apply hP _ hΩ, spectralMeasure_apply hP _ hΩ,
    map_smul, nnnorm_smul, smul_eq_mul]
  push_cast; ring

lemma spectralMeasure_zero (hP : IsProjValuedMeasure P) :
    spectralMeasure P (0 : H) = 0 := by
  ext Ω hΩ
  rw [spectralMeasure_apply hP _ hΩ]
  simp

lemma spectralMeasure_add_le (hP : IsProjValuedMeasure P) (ψ φ : H) :
    spectralMeasure P (ψ + φ) ≤ 2 • spectralMeasure P ψ + 2 • spectralMeasure P φ := by
  rw [Measure.le_iff]
  intro Ω hΩ
  rw [Measure.add_apply, Measure.smul_apply, Measure.smul_apply, spectralMeasure_apply hP _ hΩ,
    spectralMeasure_apply hP _ hΩ, spectralMeasure_apply hP _ hΩ, map_add]
  have : ‖P Ω ψ + P Ω φ‖₊ ^ 2 ≤ 2 * ‖P Ω ψ‖₊ ^ 2 + 2 * ‖P Ω φ‖₊ ^ 2 := by
    rw [← NNReal.coe_le_coe]
    push_cast
    nlinarith [norm_add_le (P Ω ψ) (P Ω φ), norm_nonneg (P Ω ψ), norm_nonneg (P Ω φ),
      sq_nonneg (‖P Ω ψ‖ - ‖P Ω φ‖), norm_nonneg (P Ω ψ + P Ω φ)]
  simp only [nsmul_eq_mul]
  exact_mod_cast this

lemma spectralMeasure_proj (hP : IsProjValuedMeasure P) {Ω : Set ℝ} (hΩ : MeasurableSet Ω)
    (ψ : H) : spectralMeasure P (P Ω ψ) = (spectralMeasure P ψ).restrict Ω := by
  ext A hA
  rw [Measure.restrict_apply hA, spectralMeasure_apply hP _ hA,
    spectralMeasure_apply hP _ (hA.inter hΩ), ← ContinuousLinearMap.mul_apply,
    ← pvm_inter hP hA hΩ]

/-! ### The domain `𝔇_f` -/

/-- `𝔇_f` as a submodule. -/
def domSub (hP : IsProjValuedMeasure P) (f : ℝ → ℂ) : Submodule ℂ H where
  carrier := spectralDomain P f
  zero_mem' := by simp [spectralDomain, spectralMeasure_zero hP]
  add_mem' := by
    intro a b ha hb
    simp only [spectralDomain, Set.mem_setOf_eq] at *
    calc _ ≤ ∫⁻ x, (‖f x‖₊ : ℝ≥0∞) ^ 2 ∂(2 • spectralMeasure P a + 2 • spectralMeasure P b) :=
          lintegral_mono' (spectralMeasure_add_le hP a b) le_rfl
      _ = 2 * ∫⁻ x, (‖f x‖₊ : ℝ≥0∞) ^ 2 ∂spectralMeasure P a +
          2 * ∫⁻ x, (‖f x‖₊ : ℝ≥0∞) ^ 2 ∂spectralMeasure P b := by
          rw [lintegral_add_measure, lintegral_smul_measure, lintegral_smul_measure]
          simp [nsmul_eq_mul]
      _ < ∞ := ENNReal.add_lt_top.2 ⟨ENNReal.mul_lt_top (by simp) ha,
          ENNReal.mul_lt_top (by simp) hb⟩
  smul_mem' := by
    intro c a ha
    simp only [spectralDomain, Set.mem_setOf_eq] at *
    rw [spectralMeasure_smul hP, lintegral_smul_measure, smul_eq_mul]
    exact ENNReal.mul_lt_top (by simp) ha

lemma mem_domSub {hP : IsProjValuedMeasure P} {f : ℝ → ℂ} {ψ : H} :
    ψ ∈ domSub hP f ↔ ψ ∈ spectralDomain P f := Iff.rfl

/-! ### Truncations -/

/-- `{x | ‖f x‖ ≤ n}` -/
def truncSet (f : ℝ → ℂ) (n : ℕ) : Set ℝ := {x | ‖f x‖ ≤ n}

/-- `f · 1_{‖f‖ ≤ n}` -/
noncomputable def trunc (f : ℝ → ℂ) (n : ℕ) : ℝ → ℂ := (truncSet f n).indicator f

lemma measurableSet_truncSet {f : ℝ → ℂ} (hf : Measurable f) (n : ℕ) :
    MeasurableSet (truncSet f n) :=
  measurableSet_le hf.norm measurable_const

lemma norm_trunc_le (f : ℝ → ℂ) (n : ℕ) (x : ℝ) : ‖trunc f n x‖ ≤ ‖f x‖ := by
  unfold trunc
  by_cases hx : x ∈ truncSet f n
  · rw [Set.indicator_of_mem hx]
  · rw [Set.indicator_of_notMem hx, norm_zero]; exact norm_nonneg _

lemma ibb_trunc {f : ℝ → ℂ} (hf : Measurable f) (n : ℕ) : IsBoundedBorel (trunc f n) := by
  refine ⟨hf.indicator (measurableSet_truncSet hf n), n, fun x => ?_⟩
  unfold trunc
  by_cases hx : x ∈ truncSet f n
  · rw [Set.indicator_of_mem hx]; exact hx
  · rw [Set.indicator_of_notMem hx, norm_zero]; positivity

lemma trunc_eventually (f : ℝ → ℂ) (x : ℝ) : ∀ᶠ n in Filter.atTop, trunc f n x = f x := by
  obtain ⟨N, hN⟩ := exists_nat_ge ‖f x‖
  filter_upwards [Filter.eventually_ge_atTop N] with n hn
  have hx : x ∈ truncSet f n := show ‖f x‖ ≤ (n : ℝ) from hN.trans (by exact_mod_cast hn)
  exact Set.indicator_of_mem hx f

lemma tendsto_trunc (f : ℝ → ℂ) (x : ℝ) :
    Filter.Tendsto (fun n => trunc f n x) Filter.atTop (nhds (f x)) :=
  tendsto_const_nhds.congr' ((trunc_eventually f x).mono fun _ h => h.symm)

lemma integrable_normSq_of_mem {f : ℝ → ℂ} (hf : Measurable f) {ψ : H}
    (hψ : ψ ∈ spectralDomain P f) :
    Integrable (fun x => ‖f x‖ ^ 2) (spectralMeasure P ψ) := by
  refine ⟨(hf.norm.pow_const 2).aestronglyMeasurable, ?_⟩
  unfold HasFiniteIntegral
  convert hψ using 3 with x
  simp [enorm_pow]
  rfl

lemma integrable_of_mem (hP : IsProjValuedMeasure P) {f : ℝ → ℂ} (hf : Measurable f) {ψ : H}
    (hψ : ψ ∈ spectralDomain P f) : Integrable f (spectralMeasure P ψ) := by
  haveI := spectralMeasure_finite hP ψ
  refine Integrable.mono' ((integrable_const 1).add (integrable_normSq_of_mem hf hψ))
    hf.aestronglyMeasurable (Filter.Eventually.of_forall fun x => ?_)
  simp only [Pi.add_apply]
  nlinarith [sq_nonneg (‖f x‖ - 1), norm_nonneg (f x)]

lemma norm_bsi_sub_sq (hP : IsProjValuedMeasure P) {g h : ℝ → ℂ} (hg : IsBoundedBorel g)
    (hh : IsBoundedBorel h) (ψ : H) :
    ‖boundedSpectralIntegral P g ψ - boundedSpectralIntegral P h ψ‖ ^ 2 =
      ∫ x, ‖g x - h x‖ ^ 2 ∂spectralMeasure P ψ := by
  rw [← ContinuousLinearMap.sub_apply, ← bsi_sub hP hg hh, bsi_norm_sq hP (ibb_sub hg hh)]
  rfl

/-- Dominated convergence for `∫ ‖Fₙ‖²` with an integrable dominating function `4‖f‖²`. -/
lemma tendsto_integral_normSq {f : ℝ → ℂ} (hf : Measurable f)
    {ψ : H} (hψ : ψ ∈ spectralDomain P f) {F : ℕ → ℝ → ℂ} (hFm : ∀ n, Measurable (F n))
    (hFb : ∀ n x, ‖F n x‖ ≤ 2 * ‖f x‖)
    (hFl : ∀ x, Filter.Tendsto (fun n => F n x) Filter.atTop (nhds 0)) :
    Filter.Tendsto (fun n => ∫ x, ‖F n x‖ ^ 2 ∂spectralMeasure P ψ) Filter.atTop (nhds 0) := by
  have := tendsto_integral_of_dominated_convergence (μ := spectralMeasure P ψ)
    (F := fun n x => ‖F n x‖ ^ 2) (f := fun _ => 0) (fun x => 4 * ‖f x‖ ^ 2)
    (fun n => ((hFm n).norm.pow_const 2).aestronglyMeasurable)
    ((integrable_normSq_of_mem hf hψ).const_mul 4)
    (fun n => Filter.Eventually.of_forall (fun x => by
      rw [Real.norm_of_nonneg (by positivity)]
      have := hFb n x
      nlinarith [norm_nonneg (F n x)]))
    (Filter.Eventually.of_forall (fun x => by
      have := ((hFl x).norm).pow 2
      simpa using this))
  simpa using this

/-! ### Construction of the unbounded spectral integral -/

lemma cauchySeq_bsi_trunc (hP : IsProjValuedMeasure P) {f : ℝ → ℂ} (hf : Measurable f) {ψ : H}
    (hψ : ψ ∈ spectralDomain P f) :
    CauchySeq (fun n => boundedSpectralIntegral P (trunc f n) ψ) := by
  -- tails `tₙ = ∫ ‖f - trunc f n‖²` tend to zero
  have ht := tendsto_integral_normSq hf hψ (F := fun n x => f x - trunc f n x)
    (fun n => hf.sub (ibb_trunc hf n).1)
    (fun n x => by
      have := norm_trunc_le f n x
      calc ‖f x - trunc f n x‖ ≤ ‖f x‖ + ‖trunc f n x‖ := norm_sub_le _ _
        _ ≤ 2 * ‖f x‖ := by linarith)
    (fun x => by simpa using (tendsto_trunc f x).const_sub (f x))
  rw [Metric.cauchySeq_iff]
  intro ε hε
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 ht ((ε / 2) ^ 2) (by positivity)
  refine ⟨N, fun m hm n hn => ?_⟩
  rw [dist_eq_norm]
  -- `‖B(trunc m)ψ - B(trunc n)ψ‖ ≤ ‖B(trunc m)ψ - ?‖ ...` via the `L²` comparison with `f`
  have key : ∀ k ≥ N, ∀ l ≥ k,
      ‖boundedSpectralIntegral P (trunc f k) ψ - boundedSpectralIntegral P (trunc f l) ψ‖ ^ 2
        < (ε / 2) ^ 2 := by
    intro k hk l hl
    rw [norm_bsi_sub_sq hP (ibb_trunc hf k) (ibb_trunc hf l)]
    have h1 := hN k hk
    rw [Real.dist_eq, sub_zero] at h1
    refine lt_of_le_of_lt ?_ (le_abs_self _ |>.trans_lt h1)
    haveI := spectralMeasure_finite hP ψ
    show _ ≤ ∫ x, ‖f x - trunc f k x‖ ^ 2 ∂spectralMeasure P ψ
    refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun x => by positivity)
      ((integrable_normSq_of_mem hf hψ).mono' ((hf.sub (ibb_trunc hf k).1).norm.pow_const 2
        |>.aestronglyMeasurable) (Filter.Eventually.of_forall fun x => ?_)) ?_
    · rw [Real.norm_of_nonneg (by positivity)]
      apply pow_le_pow_left₀ (norm_nonneg _)
      simp only [trunc, truncSet]
      by_cases h1 : ‖f x‖ ≤ (k : ℝ)
      · rw [Set.indicator_of_mem (show x ∈ {x | ‖f x‖ ≤ (k:ℝ)} from h1), sub_self, norm_zero]
        exact norm_nonneg _
      · rw [Set.indicator_of_notMem (show x ∉ {x | ‖f x‖ ≤ (k:ℝ)} from h1), sub_zero]
    · refine Filter.Eventually.of_forall fun x => ?_
      apply pow_le_pow_left₀ (norm_nonneg _)
      simp only [trunc, truncSet]
      by_cases h1 : ‖f x‖ ≤ (k : ℝ)
      · have h2 : ‖f x‖ ≤ (l : ℝ) := h1.trans (by exact_mod_cast hl)
        rw [Set.indicator_of_mem (show x ∈ {x | ‖f x‖ ≤ (k:ℝ)} from h1),
          Set.indicator_of_mem (show x ∈ {x | ‖f x‖ ≤ (l:ℝ)} from h2), sub_self]
      · rw [Set.indicator_of_notMem (show x ∉ {x | ‖f x‖ ≤ (k:ℝ)} from h1), zero_sub,
          norm_neg, sub_zero]
        by_cases h2 : ‖f x‖ ≤ (l : ℝ)
        · rw [Set.indicator_of_mem (show x ∈ {x | ‖f x‖ ≤ (l:ℝ)} from h2)]
        · rw [Set.indicator_of_notMem (show x ∉ {x | ‖f x‖ ≤ (l:ℝ)} from h2), norm_zero]
          exact norm_nonneg _
  have hlt : ∀ k ≥ N, ∀ l ≥ k,
      ‖boundedSpectralIntegral P (trunc f k) ψ - boundedSpectralIntegral P (trunc f l) ψ‖
        < ε / 2 := by
    intro k hk l hl
    exact (pow_lt_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 (key k hk l hl)
  rcases le_total m n with hmn | hmn
  · linarith [hlt m hm n hmn]
  · rw [norm_sub_rev]; linarith [hlt n hn m hmn]

open Filter in
/-- The limit `lim B(trunc f n) ψ`. -/
noncomputable def ulim (P : Set ℝ → (H →L[ℂ] H)) (f : ℝ → ℂ) (ψ : H) : H :=
  limUnder atTop (fun n => boundedSpectralIntegral P (trunc f n) ψ)

lemma tendsto_ulim (hP : IsProjValuedMeasure P) {f : ℝ → ℂ} (hf : Measurable f) {ψ : H}
    (hψ : ψ ∈ spectralDomain P f) :
    Filter.Tendsto (fun n => boundedSpectralIntegral P (trunc f n) ψ) Filter.atTop
      (nhds (ulim P f ψ)) :=
  (cauchySeq_bsi_trunc hP hf hψ).tendsto_limUnder

/-- The unbounded spectral integral, constructed. -/
noncomputable def uInt (hP : IsProjValuedMeasure P) {f : ℝ → ℂ} (hf : Measurable f) :
    H →ₗ.[ℂ] H where
  domain := domSub hP f
  toFun :=
    { toFun := fun ψ => ulim P f ψ
      map_add' := by
        intro a b
        have ha := tendsto_ulim hP hf a.2
        have hb := tendsto_ulim hP hf b.2
        have hab := tendsto_ulim hP hf (a + b).2
        refine tendsto_nhds_unique hab ?_
        simp only [Submodule.coe_add, map_add]
        exact ha.add hb
      map_smul' := by
        intro c a
        have ha := tendsto_ulim hP hf a.2
        have hca := tendsto_ulim hP hf (c • a).2
        refine tendsto_nhds_unique hca ?_
        simp only [Submodule.coe_smul, map_smul, RingHom.id_apply]
        exact ha.const_smul c }

lemma uInt_apply (hP : IsProjValuedMeasure P) {f : ℝ → ℂ} (hf : Measurable f)
    (ψ : (uInt hP hf).domain) : uInt hP hf ψ = ulim P f ψ := rfl

/-- General convergence: dominated bounded approximants converge to `ulim`. -/
lemma tendsto_bsi_ulim (hP : IsProjValuedMeasure P) {f : ℝ → ℂ} (hf : Measurable f) {ψ : H}
    (hψ : ψ ∈ spectralDomain P f) {hs : ℕ → ℝ → ℂ} (hhs : ∀ n, IsBoundedBorel (hs n))
    (hbound : ∀ n x, ‖hs n x‖ ≤ ‖f x‖)
    (hlim : ∀ x, Filter.Tendsto (fun n => hs n x) Filter.atTop (nhds (f x))) :
    Filter.Tendsto (fun n => boundedSpectralIntegral P (hs n) ψ) Filter.atTop
      (nhds (ulim P f ψ)) := by
  have h0 : Filter.Tendsto (fun n => boundedSpectralIntegral P (hs n) ψ -
      boundedSpectralIntegral P (trunc f n) ψ) Filter.atTop (nhds 0) := by
    have ht := tendsto_integral_normSq hf hψ (F := fun n x => hs n x - trunc f n x)
      (fun n => (hhs n).1.sub (ibb_trunc hf n).1)
      (fun n x => by
        have := norm_trunc_le f n x
        have := hbound n x
        calc ‖hs n x - trunc f n x‖ ≤ ‖hs n x‖ + ‖trunc f n x‖ := norm_sub_le _ _
          _ ≤ 2 * ‖f x‖ := by linarith)
      (fun x => by simpa using (hlim x).sub (tendsto_trunc f x))
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have e : ∀ n, ‖boundedSpectralIntegral P (hs n) ψ - boundedSpectralIntegral P (trunc f n) ψ‖
        = Real.sqrt (∫ x, ‖hs n x - trunc f n x‖ ^ 2 ∂spectralMeasure P ψ) := by
      intro n
      rw [← norm_bsi_sub_sq hP (hhs n) (ibb_trunc hf n), Real.sqrt_sq (norm_nonneg _)]
    simp_rw [e]
    rw [← Real.sqrt_zero]
    exact (Real.continuous_sqrt.tendsto 0).comp ht
  have := h0.add (tendsto_ulim hP hf hψ)
  simpa using this

lemma norm_ulim_sq (hP : IsProjValuedMeasure P) {f : ℝ → ℂ} (hf : Measurable f) {ψ : H}
    (hψ : ψ ∈ spectralDomain P f) :
    ‖ulim P f ψ‖ ^ 2 = ∫ x, ‖f x‖ ^ 2 ∂spectralMeasure P ψ := by
  have h1 : Filter.Tendsto (fun n => ‖boundedSpectralIntegral P (trunc f n) ψ‖ ^ 2)
      Filter.atTop (nhds (‖ulim P f ψ‖ ^ 2)) :=
    ((tendsto_ulim hP hf hψ).norm).pow 2
  have h2 : Filter.Tendsto (fun n => ‖boundedSpectralIntegral P (trunc f n) ψ‖ ^ 2)
      Filter.atTop (nhds (∫ x, ‖f x‖ ^ 2 ∂spectralMeasure P ψ)) := by
    simp_rw [bsi_norm_sq hP (ibb_trunc hf _)]
    refine tendsto_integral_of_dominated_convergence (fun x => ‖f x‖ ^ 2)
      (fun n => ((ibb_trunc hf n).1.norm.pow_const 2).aestronglyMeasurable)
      (integrable_normSq_of_mem hf hψ)
      (fun n => Filter.Eventually.of_forall fun x => ?_)
      (Filter.Eventually.of_forall fun x => ((tendsto_trunc f x).norm).pow 2)
    rw [Real.norm_of_nonneg (by positivity)]
    exact pow_le_pow_left₀ (norm_nonneg _) (norm_trunc_le f n x) 2
  exact tendsto_nhds_unique h1 h2

lemma inner_ulim (hP : IsProjValuedMeasure P) {f : ℝ → ℂ} (hf : Measurable f) {ψ : H}
    (hψ : ψ ∈ spectralDomain P f) :
    ⟪ψ, ulim P f ψ⟫_ℂ = ∫ x, f x ∂spectralMeasure P ψ := by
  have h1 : Filter.Tendsto (fun n => ⟪ψ, boundedSpectralIntegral P (trunc f n) ψ⟫_ℂ)
      Filter.atTop (nhds ⟪ψ, ulim P f ψ⟫_ℂ) :=
    Filter.Tendsto.inner tendsto_const_nhds (tendsto_ulim hP hf hψ)
  have h2 : Filter.Tendsto (fun n => ⟪ψ, boundedSpectralIntegral P (trunc f n) ψ⟫_ℂ)
      Filter.atTop (nhds (∫ x, f x ∂spectralMeasure P ψ)) := by
    have : ∀ n, ⟪ψ, boundedSpectralIntegral P (trunc f n) ψ⟫_ℂ =
        ∫ x, trunc f n x ∂spectralMeasure P ψ := fun n => rep_bsi hP (ibb_trunc hf n) ψ
    simp_rw [this]
    exact tendsto_integral_of_dominated_convergence (fun x => ‖f x‖)
      (fun n => (ibb_trunc hf n).1.aestronglyMeasurable)
      (integrable_of_mem hP hf hψ).norm
      (fun n => Filter.Eventually.of_forall fun x => norm_trunc_le f n x)
      (Filter.Eventually.of_forall fun x => tendsto_trunc f x)
  exact tendsto_nhds_unique h1 h2

lemma isSpectralIntegral_uInt (hP : IsProjValuedMeasure P) {f : ℝ → ℂ} (hf : Measurable f) :
    IsSpectralIntegral P f (uInt hP hf) :=
  ⟨rfl, fun ψ => inner_ulim hP hf ψ.2⟩

/-! ### Density of the domain and uniqueness -/

lemma proj_truncSet_mem (hP : IsProjValuedMeasure P) {f : ℝ → ℂ} (hf : Measurable f) (n : ℕ)
    (ψ : H) : P (truncSet f n) ψ ∈ spectralDomain P f := by
  simp only [spectralDomain, Set.mem_setOf_eq]
  rw [spectralMeasure_proj hP (measurableSet_truncSet hf n)]
  haveI := spectralMeasure_finite hP ψ
  calc ∫⁻ x in truncSet f n, (‖f x‖₊ : ℝ≥0∞) ^ 2 ∂spectralMeasure P ψ
      ≤ ∫⁻ _x in truncSet f n, ((n : ℝ≥0∞)) ^ 2 ∂spectralMeasure P ψ := by
        apply setLIntegral_mono (by fun_prop)
        intro x hx
        gcongr
        have : ‖f x‖ ≤ n := hx
        exact_mod_cast (show (‖f x‖₊ : ℝ) ≤ n from this)
    _ < ∞ := by
        rw [setLIntegral_const]
        exact ENNReal.mul_lt_top (by simp) (measure_lt_top _ _)

lemma truncSet_eventually (f : ℝ → ℂ) (x : ℝ) : ∀ᶠ n in Filter.atTop, x ∈ truncSet f n := by
  obtain ⟨N, hN⟩ := exists_nat_ge ‖f x‖
  filter_upwards [Filter.eventually_ge_atTop N] with n hn
  exact show ‖f x‖ ≤ (n : ℝ) from hN.trans (by exact_mod_cast hn)

lemma tendsto_proj_truncSet (hP : IsProjValuedMeasure P) {f : ℝ → ℂ} (hf : Measurable f)
    (ψ : H) : Filter.Tendsto (fun n => P (truncSet f n) ψ) Filter.atTop (nhds ψ) := by
  have h := (bounded_functional_calculus P hP).2.2.2.2.2.2
    (fun n => (truncSet f n).indicator 1) 1
    (fun n => isBoundedBorel_indicator (measurableSet_truncSet hf n))
    (fun x => tendsto_const_nhds.congr' (by
      filter_upwards [truncSet_eventually f x] with n hn
      simp [hn]))
    ⟨1, fun n x => by by_cases hx : x ∈ truncSet f n <;> simp [hx]⟩ ψ
  rw [(bounded_functional_calculus P hP).1] at h
  simpa [bsi_indicator hP (measurableSet_truncSet hf _)] using h

lemma dense_spectralDomain (hP : IsProjValuedMeasure P) {f : ℝ → ℂ} (hf : Measurable f) :
    Dense (spectralDomain P f) := by
  intro ψ
  exact mem_closure_of_tendsto (tendsto_proj_truncSet hP hf ψ)
    (Filter.Eventually.of_forall fun n => proj_truncSet_mem hP hf n ψ)


omit [CompleteSpace H] in
lemma lpm_polarization (T : H →ₗ.[ℂ] H) (φ ψ : T.domain) :
    ⟪(φ : H), T ψ⟫_ℂ = (1/4 : ℂ) * (⟪((φ + ψ : T.domain) : H), T (φ + ψ)⟫_ℂ -
      ⟪((φ - ψ : T.domain) : H), T (φ - ψ)⟫_ℂ +
      Complex.I * ⟪((φ - Complex.I • ψ : T.domain) : H), T (φ - Complex.I • ψ)⟫_ℂ -
      Complex.I * ⟪((φ + Complex.I • ψ : T.domain) : H), T (φ + Complex.I • ψ)⟫_ℂ) := by
  simp only [LinearPMap.map_add, LinearPMap.map_sub, LinearPMap.map_smul, Submodule.coe_add,
    Submodule.coe_sub, Submodule.coe_smul, inner_add_left, inner_add_right, inner_sub_left,
    inner_sub_right, inner_smul_left, inner_smul_right, Complex.conj_I]
  ring_nf
  simp only [Complex.I_sq]
  ring

omit [CompleteSpace H] in
/-- A densely defined operator is determined by its quadratic form. -/
lemma lpm_eq_of_inner_self {T S : H →ₗ.[ℂ] H} (hdom : T.domain = S.domain)
    (hdense : Dense (T.domain : Set H))
    (h : ∀ (x : H) (hx : x ∈ T.domain) (hx' : x ∈ S.domain),
      ⟪x, T ⟨x, hx⟩⟫_ℂ = ⟪x, S ⟨x, hx'⟩⟫_ℂ) : T = S := by
  refine LinearPMap.ext hdom (fun x hx hx' => ?_)
  set v := T ⟨x, hx⟩ - S ⟨x, hx'⟩
  have horth : ∀ φ ∈ T.domain, ⟪φ, v⟫_ℂ = 0 := by
    intro φ hφ
    have hS : ∀ (a : H) (ha : a ∈ S.domain), ⟪φ, S ⟨a, ha⟩⟫_ℂ = (1/4 : ℂ) *
        (⟪φ + a, S ⟨φ + a, S.domain.add_mem (hdom ▸ hφ) ha⟩⟫_ℂ -
         ⟪φ - a, S ⟨φ - a, S.domain.sub_mem (hdom ▸ hφ) ha⟩⟫_ℂ +
         Complex.I * ⟪φ - Complex.I • a, S ⟨φ - Complex.I • a,
           S.domain.sub_mem (hdom ▸ hφ) (S.domain.smul_mem _ ha)⟩⟫_ℂ -
         Complex.I * ⟪φ + Complex.I • a, S ⟨φ + Complex.I • a,
           S.domain.add_mem (hdom ▸ hφ) (S.domain.smul_mem _ ha)⟩⟫_ℂ) := fun a ha =>
      lpm_polarization S ⟨φ, hdom ▸ hφ⟩ ⟨a, ha⟩
    have hT : ∀ (a : H) (ha : a ∈ T.domain), ⟪φ, T ⟨a, ha⟩⟫_ℂ = (1/4 : ℂ) *
        (⟪φ + a, T ⟨φ + a, T.domain.add_mem hφ ha⟩⟫_ℂ -
         ⟪φ - a, T ⟨φ - a, T.domain.sub_mem hφ ha⟩⟫_ℂ +
         Complex.I * ⟪φ - Complex.I • a, T ⟨φ - Complex.I • a,
           T.domain.sub_mem hφ (T.domain.smul_mem _ ha)⟩⟫_ℂ -
         Complex.I * ⟪φ + Complex.I • a, T ⟨φ + Complex.I • a,
           T.domain.add_mem hφ (T.domain.smul_mem _ ha)⟩⟫_ℂ) := fun a ha =>
      lpm_polarization T ⟨φ, hφ⟩ ⟨a, ha⟩
    simp only [v, inner_sub_right]
    rw [hT x hx, hS x hx']
    rw [h _ (T.domain.add_mem hφ hx), h _ (T.domain.sub_mem hφ hx),
      h _ (T.domain.sub_mem hφ (T.domain.smul_mem _ hx)),
      h _ (T.domain.add_mem hφ (T.domain.smul_mem _ hx)), sub_self]
    all_goals first
      | exact S.domain.add_mem (hdom ▸ hφ) (S.domain.smul_mem _ hx')
      | exact S.domain.sub_mem (hdom ▸ hφ) (S.domain.smul_mem _ hx')
      | exact S.domain.add_mem (hdom ▸ hφ) hx'
      | exact S.domain.sub_mem (hdom ▸ hφ) hx'
  have hclosed : IsClosed {φ : H | ⟪φ, v⟫_ℂ = 0} :=
    isClosed_eq (continuous_id.inner continuous_const) continuous_const
  have hall : {φ : H | ⟪φ, v⟫_ℂ = 0} = Set.univ := by
    apply Set.eq_univ_of_univ_subset
    rw [← hdense.closure_eq]
    exact hclosed.closure_subset_iff.2 horth
  have hv : ⟪v, v⟫_ℂ = 0 := by
    have : v ∈ {φ : H | ⟪φ, v⟫_ℂ = 0} := by rw [hall]; trivial
    exact this
  exact sub_eq_zero.1 (inner_self_eq_zero.1 hv)

lemma isSpectralIntegral_unique (hP : IsProjValuedMeasure P) {f : ℝ → ℂ} (hf : Measurable f)
    {T S : H →ₗ.[ℂ] H} (hT : IsSpectralIntegral P f T) (hS : IsSpectralIntegral P f S) :
    T = S := by
  have hdom : T.domain = S.domain := SetLike.coe_injective (hT.1.trans hS.1.symm)
  apply lpm_eq_of_inner_self hdom (by rw [hT.1]; exact dense_spectralDomain hP hf)
  intro x hx hx'
  rw [hT.2 ⟨x, hx⟩, hS.2 ⟨x, hx'⟩]

lemma spectralIntegral_eq_uInt (hP : IsProjValuedMeasure P) {f : ℝ → ℂ} (hf : Measurable f) :
    spectralIntegral P f = uInt hP hf := by
  have h : ∃ T, IsSpectralIntegral P f T := ⟨_, isSpectralIntegral_uInt hP hf⟩
  unfold spectralIntegral
  rw [dif_pos h]
  exact isSpectralIntegral_unique hP hf h.choose_spec (isSpectralIntegral_uInt hP hf)

lemma isSpectralIntegral_spectralIntegral (hP : IsProjValuedMeasure P) {f : ℝ → ℂ}
    (hf : Measurable f) : IsSpectralIntegral P f (spectralIntegral P f) := by
  rw [spectralIntegral_eq_uInt hP hf]; exact isSpectralIntegral_uInt hP hf

end TeschlQM.Spectral.BFC


open MeasureTheory
open scoped ENNReal InnerProductSpace

namespace TeschlQM.Spectral.BFC

open TeschlQM.Shared TeschlQM.Spectral

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {P : Set ℝ → (H →L[ℂ] H)}

lemma nnsq_eq {E : Type*} [SeminormedAddCommGroup E] (z : E) : (‖z‖₊ : ℝ≥0∞) ^ 2 = ENNReal.ofReal (‖z‖ ^ 2) := by
  rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm_eq_enorm]; rfl

lemma ibb_trunc_bound (f : ℝ → ℂ) (n : ℕ) (x : ℝ) : ‖trunc f n x‖ ≤ n := by
  unfold trunc
  by_cases hx : x ∈ truncSet f n
  · rw [Set.indicator_of_mem hx]; exact hx
  · rw [Set.indicator_of_notMem hx, norm_zero]; positivity

lemma mem_spectralDomain_of_le {f g F : ℝ → ℂ} (hf : Measurable f) (hg : Measurable g)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hF : ∀ x, ‖F x‖ ≤ a * ‖f x‖ + b * ‖g x‖) {ψ : H}
    (hψf : ψ ∈ spectralDomain P f) (hψg : ψ ∈ spectralDomain P g) :
    ψ ∈ spectralDomain P F := by
  simp only [spectralDomain, Set.mem_setOf_eq] at *
  have hpt : ∀ x, (‖F x‖₊ : ℝ≥0∞) ^ 2 ≤ ENNReal.ofReal (2 * a ^ 2) * (‖f x‖₊ : ℝ≥0∞) ^ 2 +
      ENNReal.ofReal (2 * b ^ 2) * (‖g x‖₊ : ℝ≥0∞) ^ 2 := by
    intro x
    have h1 : ‖F x‖ ^ 2 ≤ 2 * a ^ 2 * ‖f x‖ ^ 2 + 2 * b ^ 2 * ‖g x‖ ^ 2 := by
      have := hF x
      have h0 : 0 ≤ ‖F x‖ := norm_nonneg _
      nlinarith [sq_nonneg (a * ‖f x‖ - b * ‖g x‖), mul_nonneg ha (norm_nonneg (f x)),
        mul_nonneg hb (norm_nonneg (g x))]
    rw [nnsq_eq, nnsq_eq, nnsq_eq, ← ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_add (by positivity) (by positivity)]
    exact ENNReal.ofReal_le_ofReal (by linarith)
  calc ∫⁻ x, (‖F x‖₊ : ℝ≥0∞) ^ 2 ∂spectralMeasure P ψ
      ≤ ∫⁻ x, (ENNReal.ofReal (2 * a ^ 2) * (‖f x‖₊ : ℝ≥0∞) ^ 2 +
          ENNReal.ofReal (2 * b ^ 2) * (‖g x‖₊ : ℝ≥0∞) ^ 2) ∂spectralMeasure P ψ :=
        lintegral_mono hpt
    _ = ENNReal.ofReal (2 * a ^ 2) * ∫⁻ x, (‖f x‖₊ : ℝ≥0∞) ^ 2 ∂spectralMeasure P ψ +
          ENNReal.ofReal (2 * b ^ 2) * ∫⁻ x, (‖g x‖₊ : ℝ≥0∞) ^ 2 ∂spectralMeasure P ψ := by
        rw [lintegral_add_left (by fun_prop), lintegral_const_mul _ (by fun_prop),
          lintegral_const_mul _ (by fun_prop)]
    _ < ∞ := ENNReal.add_lt_top.2 ⟨ENNReal.mul_lt_top ENNReal.ofReal_lt_top hψf,
        ENNReal.mul_lt_top ENNReal.ofReal_lt_top hψg⟩

lemma mem_spectralDomain_mono {f F : ℝ → ℂ} (hf : Measurable f) {a : ℝ} (ha : 0 ≤ a)
    (hF : ∀ x, ‖F x‖ ≤ a * ‖f x‖) {ψ : H} (hψf : ψ ∈ spectralDomain P f) :
    ψ ∈ spectralDomain P F :=
  mem_spectralDomain_of_le hf hf ha le_rfl (fun x => by simpa using hF x) hψf hψf

/-- Convergence of dominated approximants, with a general dominating function `G`. -/
lemma tendsto_bsi_ulim' (hP : IsProjValuedMeasure P) {f G : ℝ → ℂ} (hf : Measurable f)
    (hG : Measurable G) {ψ : H} (hψ : ψ ∈ spectralDomain P f) (hψG : ψ ∈ spectralDomain P G)
    (hfG : ∀ x, ‖f x‖ ≤ ‖G x‖) {hs : ℕ → ℝ → ℂ} (hhs : ∀ n, IsBoundedBorel (hs n))
    (hbound : ∀ n x, ‖hs n x‖ ≤ ‖G x‖)
    (hlim : ∀ x, Filter.Tendsto (fun n => hs n x) Filter.atTop (nhds (f x))) :
    Filter.Tendsto (fun n => boundedSpectralIntegral P (hs n) ψ) Filter.atTop
      (nhds (ulim P f ψ)) := by
  have h0 : Filter.Tendsto (fun n => boundedSpectralIntegral P (hs n) ψ -
      boundedSpectralIntegral P (trunc f n) ψ) Filter.atTop (nhds 0) := by
    have ht := tendsto_integral_normSq hG hψG (F := fun n x => hs n x - trunc f n x)
      (fun n => (hhs n).1.sub (ibb_trunc hf n).1)
      (fun n x => by
        have := norm_trunc_le f n x
        have := hbound n x
        have := hfG x
        calc ‖hs n x - trunc f n x‖ ≤ ‖hs n x‖ + ‖trunc f n x‖ := norm_sub_le _ _
          _ ≤ 2 * ‖G x‖ := by linarith)
      (fun x => by simpa using (hlim x).sub (tendsto_trunc f x))
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have e : ∀ n, ‖boundedSpectralIntegral P (hs n) ψ - boundedSpectralIntegral P (trunc f n) ψ‖
        = Real.sqrt (∫ x, ‖hs n x - trunc f n x‖ ^ 2 ∂spectralMeasure P ψ) := by
      intro n
      rw [← norm_bsi_sub_sq hP (hhs n) (ibb_trunc hf n), Real.sqrt_sq (norm_nonneg _)]
    simp_rw [e]
    rw [← Real.sqrt_zero]
    exact (Real.continuous_sqrt.tendsto 0).comp ht
  have := h0.add (tendsto_ulim hP hf hψ)
  simpa using this

lemma ulim_lin (hP : IsProjValuedMeasure P) {f g : ℝ → ℂ} (hf : Measurable f)
    (hg : Measurable g) (α β : ℂ) {ψ : H} (hψf : ψ ∈ spectralDomain P f)
    (hψg : ψ ∈ spectralDomain P g) :
    ulim P (α • f + β • g) ψ = α • ulim P f ψ + β • ulim P g ψ := by
  set c : ℝ := ‖α‖ + ‖β‖
  have hc : 0 ≤ c := by positivity
  set G : ℝ → ℂ := fun x => ((c * (‖f x‖ + ‖g x‖) : ℝ) : ℂ)
  have hGn : ∀ x, ‖G x‖ = c * (‖f x‖ + ‖g x‖) := fun x => by
    simp only [G, Complex.norm_real, Real.norm_eq_abs]
    exact abs_of_nonneg (by positivity)
  have hG : Measurable G :=
    Complex.measurable_ofReal.comp (measurable_const.mul (hf.norm.add hg.norm))
  have hψG : ψ ∈ spectralDomain P G :=
    mem_spectralDomain_of_le hf hg hc hc (fun x => by rw [hGn]; linarith) hψf hψg
  have hF : Measurable (α • f + β • g) := (hf.const_smul α).add (hg.const_smul β)
  have hFb : ∀ x, ‖(α • f + β • g) x‖ ≤ ‖α‖ * ‖f x‖ + ‖β‖ * ‖g x‖ := fun x => by
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    exact (norm_add_le _ _).trans (by rw [norm_mul, norm_mul])
  have hψF : ψ ∈ spectralDomain P (α • f + β • g) :=
    mem_spectralDomain_of_le hf hg (norm_nonneg _) (norm_nonneg _) hFb hψf hψg
  have hle : ∀ (u v : ℝ), 0 ≤ u → 0 ≤ v → ‖α‖ * u + ‖β‖ * v ≤ c * (u + v) := by
    intro u v hu hv
    simp only [c]
    nlinarith [norm_nonneg α, norm_nonneg β, mul_nonneg (norm_nonneg α) hv,
      mul_nonneg (norm_nonneg β) hu]
  have t := tendsto_bsi_ulim' hP hF hG hψF hψG
    (fun x => by rw [hGn]; exact (hFb x).trans (hle _ _ (norm_nonneg _) (norm_nonneg _)))
    (hs := fun n => α • trunc f n + β • trunc g n)
    (fun n => ibb_add (ibb_smul α (ibb_trunc hf n)) (ibb_smul β (ibb_trunc hg n)))
    (fun n x => by
      rw [hGn]
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      refine (norm_add_le _ _).trans ?_
      rw [norm_mul, norm_mul]
      refine le_trans ?_ (hle _ _ (norm_nonneg (f x)) (norm_nonneg (g x)))
      gcongr
      · exact norm_trunc_le f n x
      · exact norm_trunc_le g n x)
    (fun x => by
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      exact ((tendsto_trunc f x).const_mul α).add ((tendsto_trunc g x).const_mul β))
  have t2 : Filter.Tendsto (fun n => boundedSpectralIntegral P (α • trunc f n + β • trunc g n) ψ)
      Filter.atTop (nhds (α • ulim P f ψ + β • ulim P g ψ)) := by
    have e : ∀ n, boundedSpectralIntegral P (α • trunc f n + β • trunc g n) ψ =
        α • boundedSpectralIntegral P (trunc f n) ψ + β • boundedSpectralIntegral P (trunc g n) ψ := by
      intro n
      rw [bsi_add hP (ibb_smul α (ibb_trunc hf n)) (ibb_smul β (ibb_trunc hg n)),
        bsi_smul hP α (ibb_trunc hf n), bsi_smul hP β (ibb_trunc hg n)]
      rfl
    simp_rw [e]
    exact ((tendsto_ulim hP hf hψf).const_smul α).add ((tendsto_ulim hP hg hψg).const_smul β)
  exact tendsto_nhds_unique t t2

lemma bsi_ulim (hP : IsProjValuedMeasure P) {h g : ℝ → ℂ} (hh : IsBoundedBorel h)
    (hg : Measurable g) {ψ : H} (hψ : ψ ∈ spectralDomain P g) :
    boundedSpectralIntegral P h (ulim P g ψ) = ulim P (h * g) ψ := by
  obtain ⟨C, hC⟩ := hh.2
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 0)
  set G : ℝ → ℂ := fun x => ((C * ‖g x‖ : ℝ) : ℂ)
  have hGn : ∀ x, ‖G x‖ = C * ‖g x‖ := fun x => by
    simp only [G, Complex.norm_real, Real.norm_eq_abs]
    exact abs_of_nonneg (by positivity)
  have hG : Measurable G := Complex.measurable_ofReal.comp (measurable_const.mul hg.norm)
  have hψG : ψ ∈ spectralDomain P G :=
    mem_spectralDomain_mono hg hC0 (fun x => (hGn x).le) hψ
  have hhg : ∀ x, ‖(h * g) x‖ ≤ C * ‖g x‖ := fun x => by
    simp only [Pi.mul_apply, norm_mul]
    exact mul_le_mul_of_nonneg_right (hC x) (norm_nonneg _)
  have hψF : ψ ∈ spectralDomain P (h * g) := mem_spectralDomain_mono hg hC0 hhg hψ
  have t := tendsto_bsi_ulim' hP (hh.1.mul hg) hG hψF hψG (fun x => by rw [hGn]; exact hhg x)
    (hs := fun n => h * trunc g n) (fun n => ibb_mul hh (ibb_trunc hg n))
    (fun n x => by
      rw [hGn]
      simp only [Pi.mul_apply, norm_mul]
      exact mul_le_mul (hC x) (norm_trunc_le g n x) (norm_nonneg _) hC0)
    (fun x => by
      simp only [Pi.mul_apply]
      exact (tendsto_trunc g x).const_mul (h x))
  have t2 : Filter.Tendsto (fun n => boundedSpectralIntegral P (h * trunc g n) ψ)
      Filter.atTop (nhds (boundedSpectralIntegral P h (ulim P g ψ))) := by
    have e : ∀ n, boundedSpectralIntegral P (h * trunc g n) ψ =
        boundedSpectralIntegral P h (boundedSpectralIntegral P (trunc g n) ψ) := by
      intro n
      rw [bsi_mul hP hh (ibb_trunc hg n)]
      rfl
    simp_rw [e]
    exact ((boundedSpectralIntegral P h).continuous.tendsto _).comp (tendsto_ulim hP hg hψ)
  exact tendsto_nhds_unique t2 t

lemma spectralMeasure_ulim (hP : IsProjValuedMeasure P) {g : ℝ → ℂ} (hg : Measurable g)
    {ψ : H} (hψ : ψ ∈ spectralDomain P g) :
    spectralMeasure P (ulim P g ψ) =
      (spectralMeasure P ψ).withDensity (fun x => (‖g x‖₊ : ℝ≥0∞) ^ 2) := by
  ext Ω hΩ
  have hΩb := isBoundedBorel_indicator hΩ
  have hmem : ψ ∈ spectralDomain P (Ω.indicator 1 * g) :=
    mem_spectralDomain_mono hg zero_le_one (fun x => by
      simp only [Pi.mul_apply, norm_mul, one_mul]
      by_cases hx : x ∈ Ω <;> simp [hx]) hψ
  rw [spectralMeasure_apply hP _ hΩ, withDensity_apply _ hΩ, ← bsi_indicator hP hΩ,
    bsi_ulim hP hΩb hg hψ, nnsq_eq, norm_ulim_sq (f := Ω.indicator 1 * g) hP (hΩb.1.mul hg) hmem]
  haveI := spectralMeasure_finite hP ψ
  rw [ofReal_integral_eq_lintegral_ofReal
    (integrable_normSq_of_mem (f := Ω.indicator 1 * g) (hΩb.1.mul hg) hmem)
    (Filter.Eventually.of_forall fun x => by positivity), ← lintegral_indicator hΩ]
  congr 1
  funext x
  by_cases hx : x ∈ Ω
  · simp [hx, nnsq_eq]
  · simp [hx]

lemma mem_comp_iff (hP : IsProjValuedMeasure P) {f g : ℝ → ℂ} (hf : Measurable f)
    (hg : Measurable g) {ψ : H} (hψ : ψ ∈ spectralDomain P g) :
    ulim P g ψ ∈ spectralDomain P f ↔ ψ ∈ spectralDomain P (f * g) := by
  simp only [spectralDomain, Set.mem_setOf_eq]
  rw [spectralMeasure_ulim hP hg hψ, lintegral_withDensity_eq_lintegral_mul _ (by fun_prop)
    (by fun_prop)]
  congr! 3 with x
  simp only [Pi.mul_apply, nnnorm_mul, ENNReal.coe_mul]
  ring

lemma ulim_comp (hP : IsProjValuedMeasure P) {f g : ℝ → ℂ} (hf : Measurable f)
    (hg : Measurable g) {ψ : H} (hψ : ψ ∈ spectralDomain P g)
    (hψ' : ψ ∈ spectralDomain P (f * g)) :
    ulim P f (ulim P g ψ) = ulim P (f * g) ψ := by
  have hmem : ulim P g ψ ∈ spectralDomain P f := (mem_comp_iff hP hf hg hψ).2 hψ'
  have h1 := tendsto_ulim hP hf hmem
  have e : ∀ n, boundedSpectralIntegral P (trunc f n) (ulim P g ψ) =
      ulim P (trunc f n * g) ψ := fun n => bsi_ulim hP (ibb_trunc hf n) hg hψ
  simp_rw [e] at h1
  refine tendsto_nhds_unique h1 ?_
  have hmemn : ∀ n, ψ ∈ spectralDomain P (trunc f n * g) := fun n =>
    mem_spectralDomain_mono hg (Nat.cast_nonneg n) (fun x => by
      simp only [Pi.mul_apply, norm_mul]
      exact mul_le_mul_of_nonneg_right (ibb_trunc_bound f n x) (norm_nonneg _)) hψ
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have e2 : ∀ n, ‖ulim P (trunc f n * g) ψ - ulim P (f * g) ψ‖ =
      Real.sqrt (∫ x, ‖(trunc f n * g) x - (f * g) x‖ ^ 2 ∂spectralMeasure P ψ) := by
    intro n
    have hlin := ulim_lin (f := trunc f n * g) (g := f * g) hP ((ibb_trunc hf n).1.mul hg)
      (hf.mul hg) 1 (-1) (hmemn n) hψ'
    have e3 : (1:ℂ) • (trunc f n * g) + (-1:ℂ) • (f * g) = trunc f n * g - f * g := by
      rw [one_smul, neg_one_smul, ← sub_eq_add_neg]
    rw [e3, one_smul, neg_one_smul, ← sub_eq_add_neg] at hlin
    rw [← hlin, ← Real.sqrt_sq (norm_nonneg _), norm_ulim_sq (f := trunc f n * g - f * g) hP
      (((ibb_trunc hf n).1.mul hg).sub (hf.mul hg)) (mem_spectralDomain_of_le (f := trunc f n * g) (g := f * g) (F := trunc f n * g - f * g)
        ((ibb_trunc hf n).1.mul hg) (hf.mul hg) zero_le_one zero_le_one
        (fun x => by simpa using norm_sub_le ((trunc f n * g) x) ((f * g) x)) (hmemn n) hψ')]
    rfl
  simp_rw [e2]
  rw [← Real.sqrt_zero]
  apply (Real.continuous_sqrt.tendsto 0).comp
  refine tendsto_integral_normSq (f := f * g) (hf.mul hg) hψ' (F := fun n x => (trunc f n * g) x - (f * g) x)
    (fun n => ((ibb_trunc hf n).1.mul hg).sub (hf.mul hg)) (fun n x => ?_) (fun x => ?_)
  · simp only [Pi.mul_apply, ← sub_mul, norm_mul]
    have : ‖trunc f n x - f x‖ ≤ ‖f x‖ := by
      simp only [trunc]
      by_cases hx : x ∈ truncSet f n
      · rw [Set.indicator_of_mem hx, sub_self, norm_zero]; exact norm_nonneg _
      · rw [Set.indicator_of_notMem hx, zero_sub, norm_neg]
    nlinarith [norm_nonneg (g x), norm_nonneg (f x), mul_le_mul_of_nonneg_right this
      (norm_nonneg (g x))]
  · simp only [Pi.mul_apply, ← sub_mul]
    simpa using ((tendsto_trunc f x).sub_const (f x)).mul_const (g x)

end TeschlQM.Spectral.BFC

namespace TeschlQM.Spectral

open TeschlQM.Spectral.BFC

/-- Teschl, p. 94, Lemma 3.5. -/
theorem spectralIntegral_add_mul {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (P : Set ℝ → (H →L[ℂ] H)) (hP : TeschlQM.Shared.IsProjValuedMeasure P) (f g : ℝ → ℂ)
    (hf : Measurable f) (hg : Measurable g) (α β : ℂ) :
    α • spectralIntegral P f + β • spectralIntegral P g ≤ spectralIntegral P (α • f + β • g) ∧
    ((α • spectralIntegral P f + β • spectralIntegral P g).domain : Set H) =
      spectralDomain P (fun x => ((‖f x‖ + ‖g x‖ : ℝ) : ℂ)) ∧
    (∀ ψ : H, (∃ hψ : ψ ∈ (spectralIntegral P g).domain,
        spectralIntegral P g ⟨ψ, hψ⟩ ∈ (spectralIntegral P f).domain) ↔
      ψ ∈ spectralDomain P g ∩ spectralDomain P (f * g)) ∧
    (∀ (ψ : (spectralIntegral P g).domain)
        (h : spectralIntegral P g ψ ∈ (spectralIntegral P f).domain),
      ∃ h' : (ψ : H) ∈ (spectralIntegral P (f * g)).domain,
        spectralIntegral P f ⟨spectralIntegral P g ψ, h⟩ =
          spectralIntegral P (f * g) ⟨ψ, h'⟩) := by
  have hF : Measurable (α • f + β • g) := (hf.const_smul α).add (hg.const_smul β)
  have hfg : Measurable (f * g) := hf.mul hg
  rw [spectralIntegral_eq_uInt hP hf, spectralIntegral_eq_uInt hP hg,
    spectralIntegral_eq_uInt hP hF, spectralIntegral_eq_uInt hP hfg]
  have hdom : ∀ ψ : H, ψ ∈ (α • uInt hP hf + β • uInt hP hg).domain ↔
      ψ ∈ spectralDomain P f ∧ ψ ∈ spectralDomain P g := by
    intro ψ
    rw [LinearPMap.add_domain, LinearPMap.smul_domain, LinearPMap.smul_domain]
    exact Iff.rfl
  refine ⟨⟨fun ψ hψ => ?_, fun x y hxy => ?_⟩, ?_, ?_, ?_⟩
  · obtain ⟨h1, h2⟩ := (hdom ψ).1 hψ
    exact mem_spectralDomain_of_le hf hg (norm_nonneg α) (norm_nonneg β) (fun x => by
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      exact (norm_add_le _ _).trans (by rw [norm_mul, norm_mul])) h1 h2
  · obtain ⟨h1, h2⟩ := (hdom x).1 x.2
    change (α • uInt hP hf) ⟨x, _⟩ + (β • uInt hP hg) ⟨x, _⟩ = _
    rw [LinearPMap.smul_apply, LinearPMap.smul_apply, uInt_apply, uInt_apply, uInt_apply,
      ← hxy]
    exact (ulim_lin hP hf hg α β h1 h2).symm
  · ext ψ
    simp only [SetLike.mem_coe]
    rw [hdom ψ]
    constructor
    · rintro ⟨h1, h2⟩
      exact mem_spectralDomain_of_le hf hg zero_le_one zero_le_one (fun x => by
        simp only [Complex.norm_real, Real.norm_eq_abs, one_mul]
        exact (abs_of_nonneg (by positivity)).le) h1 h2
    · intro h
      have hG : Measurable (fun x => ((‖f x‖ + ‖g x‖ : ℝ) : ℂ)) :=
        Complex.measurable_ofReal.comp (hf.norm.add hg.norm)
      have hn : ∀ x, ‖((‖f x‖ + ‖g x‖ : ℝ) : ℂ)‖ = ‖f x‖ + ‖g x‖ := fun x => by
        simp only [Complex.norm_real, Real.norm_eq_abs]
        exact abs_of_nonneg (by positivity)
      exact ⟨mem_spectralDomain_mono hG zero_le_one (fun x => by
          rw [hn, one_mul]; linarith [norm_nonneg (g x)]) h,
        mem_spectralDomain_mono hG zero_le_one (fun x => by
          rw [hn, one_mul]; linarith [norm_nonneg (f x)]) h⟩
  · intro ψ
    constructor
    · rintro ⟨hψ, h⟩
      exact ⟨hψ, (mem_comp_iff hP hf hg hψ).1 h⟩
    · rintro ⟨hψ, h⟩
      exact ⟨hψ, (mem_comp_iff hP hf hg hψ).2 h⟩
  · intro ψ h
    have h' : (ψ : H) ∈ spectralDomain P (f * g) := (mem_comp_iff hP hf hg ψ.2).1 h
    exact ⟨h', ulim_comp hP hf hg ψ.2 h'⟩

end TeschlQM.Spectral


open MeasureTheory
open scoped ENNReal InnerProductSpace

namespace TeschlQM.Spectral.BFC

open TeschlQM.Shared TeschlQM.Spectral

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {P : Set ℝ → (H →L[ℂ] H)}

lemma mem_spectralDomain_const (hP : IsProjValuedMeasure P) (c : ℂ) (ψ : H) :
    ψ ∈ spectralDomain P (fun _ => c) := by
  simp only [spectralDomain, Set.mem_setOf_eq, lintegral_const]
  haveI := spectralMeasure_finite hP ψ
  exact ENNReal.mul_lt_top (by simp) (measure_lt_top _ _)

lemma mem_spectralDomain_of_bdd (hP : IsProjValuedMeasure P) {h : ℝ → ℂ}
    (hh : IsBoundedBorel h) (ψ : H) : ψ ∈ spectralDomain P h := by
  obtain ⟨C, hC⟩ := hh.2
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 0)
  exact mem_spectralDomain_mono (f := fun _ => (1 : ℂ)) measurable_const hC0
    (fun x => by simpa using hC x) (mem_spectralDomain_const hP 1 ψ)

lemma ulim_of_bdd (hP : IsProjValuedMeasure P) {h : ℝ → ℂ} (hh : IsBoundedBorel h) (ψ : H) :
    ulim P h ψ = boundedSpectralIntegral P h ψ := by
  obtain ⟨C, hC⟩ := hh.2
  refine tendsto_nhds_unique (tendsto_ulim hP hh.1 (mem_spectralDomain_of_bdd hP hh ψ))
    (tendsto_const_nhds.congr' ?_)
  obtain ⟨N, hN⟩ := exists_nat_ge C
  filter_upwards [Filter.eventually_ge_atTop N] with n hn
  have : trunc h n = h := by
    funext x
    have hx : x ∈ truncSet h n :=
      show ‖h x‖ ≤ (n : ℝ) from (hC x).trans (hN.trans (by exact_mod_cast hn))
    exact Set.indicator_of_mem hx h
  rw [this]

lemma measurable_id' : Measurable (fun x : ℝ => (x : ℂ)) := Complex.measurable_ofReal

/-- A gap in the support of `P` around `z` puts `z` in the resolvent set of `∫ λ dP`. -/
lemma resolvent_of_gap (hP : IsProjValuedMeasure P) {z : ℂ} {δ : ℝ} (hδ : 0 < δ)
    (hN : P {x : ℝ | ‖(x : ℂ) - z‖ < δ} = 0) :
    z ∈ resolventSet (uInt hP measurable_id') := by
  set N : Set ℝ := {x : ℝ | ‖(x : ℂ) - z‖ < δ}
  have hNm : MeasurableSet N :=
    measurableSet_lt ((Complex.measurable_ofReal.sub measurable_const).norm) measurable_const
  set h : ℝ → ℂ := Nᶜ.indicator (fun x => 1 / ((x : ℂ) - z))
  have hhm : Measurable h :=
    ((Complex.measurable_ofReal.sub measurable_const).const_div 1).indicator hNm.compl
  have hhb : ∀ x, ‖h x‖ ≤ 1 / δ := by
    intro x
    simp only [h]
    by_cases hx : x ∈ Nᶜ
    · rw [Set.indicator_of_mem hx]
      have : δ ≤ ‖(x : ℂ) - z‖ := not_lt.1 hx
      rw [norm_div, norm_one]
      exact one_div_le_one_div_of_le hδ this
    · rw [Set.indicator_of_notMem hx, norm_zero]; positivity
  have hhB : IsBoundedBorel h := ⟨hhm, 1 / δ, hhb⟩
  set k : ℝ → ℂ := (fun x : ℝ => (x : ℂ)) * h
  have hkB : IsBoundedBorel k := by
    refine ⟨measurable_id'.mul hhm, 1 + ‖z‖ / δ, fun x => ?_⟩
    simp only [k, Pi.mul_apply, h]
    by_cases hx : x ∈ Nᶜ
    · rw [Set.indicator_of_mem hx]
      have hd : δ ≤ ‖(x : ℂ) - z‖ := not_lt.1 hx
      have hne : (x : ℂ) - z ≠ 0 := by
        intro h0; rw [h0, norm_zero] at hd; linarith
      have e : (x : ℂ) * (1 / ((x : ℂ) - z)) = 1 + z / ((x : ℂ) - z) := by
        field_simp; ring
      rw [e]
      refine (norm_add_le _ _).trans ?_
      rw [norm_one, norm_div]
      gcongr
    · rw [Set.indicator_of_notMem hx, mul_zero, norm_zero]; positivity
  have hkey : k - z • h = Nᶜ.indicator 1 := by
    funext x
    simp only [k, h, Pi.sub_apply, Pi.mul_apply, Pi.smul_apply, smul_eq_mul]
    by_cases hx : x ∈ Nᶜ
    · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx]
      have hd : δ ≤ ‖(x : ℂ) - z‖ := not_lt.1 hx
      have hne : (x : ℂ) - z ≠ 0 := by
        intro h0; rw [h0, norm_zero] at hd; linarith
      field_simp
      simp
    · simp [Set.indicator_of_notMem hx]
  have hPc : P Nᶜ = 1 := by
    have := pvm_union hP hNm hNm.compl disjoint_compl_right
    rw [Set.union_compl_self, hP.2.1, hN, zero_add] at this
    exact this.symm
  have hB1 : boundedSpectralIntegral P (k - z • h) = 1 := by
    rw [hkey, bsi_indicator hP hNm.compl, hPc]
  have hBsplit : boundedSpectralIntegral P (k - z • h) =
      boundedSpectralIntegral P k - z • boundedSpectralIntegral P h := by
    rw [bsi_sub hP hkB (ibb_smul z hhB), bsi_smul hP z hhB]
  refine ⟨boundedSpectralIntegral P h, fun ψ => ?_, fun φ => ?_⟩
  · -- `R (A ψ - z ψ) = ψ`
    rw [uInt_apply, map_sub, map_smul, bsi_ulim hP hhB measurable_id' ψ.2,
      ulim_of_bdd hP (show IsBoundedBorel (h * fun x : ℝ => (x : ℂ)) by
        rw [mul_comm]; exact hkB)]
    have : h * (fun x : ℝ => (x : ℂ)) = k := mul_comm _ _
    rw [this]
    have := congrArg (fun T : H →L[ℂ] H => T ψ) (hBsplit.symm.trans hB1)
    simpa [ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply] using this
  · have hmem : boundedSpectralIntegral P h φ ∈ spectralDomain P (fun x : ℝ => (x : ℂ)) := by
      rw [← ulim_of_bdd hP hhB]
      exact (mem_comp_iff hP measurable_id' hhm (mem_spectralDomain_of_bdd hP hhB φ)).2
        (mem_spectralDomain_of_bdd hP hkB φ)
    refine ⟨hmem, ?_⟩
    rw [uInt_apply]
    simp only
    have e1 : ulim P (fun x : ℝ => (x : ℂ)) (boundedSpectralIntegral P h φ) =
        boundedSpectralIntegral P k φ := by
      rw [← ulim_of_bdd hP hhB, ulim_comp hP measurable_id' hhm
        (mem_spectralDomain_of_bdd hP hhB φ) (mem_spectralDomain_of_bdd hP hkB φ),
        ulim_of_bdd hP hkB]
    rw [e1]
    have := congrArg (fun T : H →L[ℂ] H => T φ) (hBsplit.symm.trans hB1)
    simpa [ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply] using this

/-- Points of the support of `P` are in the spectrum of `∫ λ dP`. -/
lemma not_resolvent_of_support (hP : IsProjValuedMeasure P) {x : ℝ}
    (hx : ∀ ε : ℝ, 0 < ε → P (Set.Ioo (x - ε) (x + ε)) ≠ 0) :
    (x : ℂ) ∉ resolventSet (uInt hP measurable_id') := by
  rintro ⟨R, hR1, -⟩
  set ε : ℝ := 1 / (‖R‖ + 1)
  have hε : 0 < ε := by positivity
  set Ω := Set.Ioo (x - ε) (x + ε)
  have hΩ : MeasurableSet Ω := measurableSet_Ioo
  obtain ⟨φ, hφ⟩ : ∃ φ, P Ω φ ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    exact hx ε hε (ContinuousLinearMap.ext hcon)
  set ψ := P Ω φ
  have hIb := isBoundedBorel_indicator hΩ
  set k : ℝ → ℂ := (fun t : ℝ => (t : ℂ)) * Ω.indicator 1
  have hkB : IsBoundedBorel k := by
    refine ⟨measurable_id'.mul hIb.1, |x| + ε, fun t => ?_⟩
    simp only [k, Pi.mul_apply]
    by_cases ht : t ∈ Ω
    · rw [Set.indicator_of_mem ht, Pi.one_apply, mul_one, Complex.norm_real, Real.norm_eq_abs]
      have := ht.1; have := ht.2
      rw [abs_le]; constructor <;> linarith [abs_nonneg x, le_abs_self x, neg_abs_le x]
    · rw [Set.indicator_of_notMem ht, mul_zero, norm_zero]; positivity
  have hψU : ψ = ulim P (Ω.indicator 1) φ := by
    rw [ulim_of_bdd hP hIb, bsi_indicator hP hΩ]
  have hmem : ψ ∈ spectralDomain P (fun t : ℝ => (t : ℂ)) := by
    rw [hψU]
    exact (mem_comp_iff hP measurable_id' hIb.1 (mem_spectralDomain_of_bdd hP hIb φ)).2
      (mem_spectralDomain_of_bdd hP hkB φ)
  have hA : ulim P (fun t : ℝ => (t : ℂ)) ψ - (x : ℂ) • ψ =
      boundedSpectralIntegral P (k - (x : ℂ) • Ω.indicator 1) φ := by
    rw [bsi_sub hP hkB (ibb_smul _ hIb), bsi_smul hP _ hIb, ContinuousLinearMap.sub_apply,
      ContinuousLinearMap.smul_apply, bsi_indicator hP hΩ]
    congr 1
    rw [hψU, ulim_comp hP measurable_id' hIb.1 (mem_spectralDomain_of_bdd hP hIb φ)
      (mem_spectralDomain_of_bdd hP hkB φ), ulim_of_bdd hP hkB]
  have hnorm : ‖ulim P (fun t : ℝ => (t : ℂ)) ψ - (x : ℂ) • ψ‖ ≤ ε * ‖ψ‖ := by
    rw [hA]
    haveI := spectralMeasure_finite hP φ
    have h1 := bsi_norm_sq hP (ibb_sub hkB (ibb_smul (x : ℂ) hIb)) φ
    have h2 := bsi_norm_sq hP hIb φ
    rw [bsi_indicator hP hΩ] at h2
    have h3 : ∫ t, ‖(k - (x : ℂ) • Ω.indicator 1 : ℝ → ℂ) t‖ ^ 2 ∂spectralMeasure P φ ≤
        ∫ t, ε ^ 2 * ‖Ω.indicator (1 : ℝ → ℂ) t‖ ^ 2 ∂spectralMeasure P φ := by
      apply integral_mono_of_nonneg (Filter.Eventually.of_forall fun t => by positivity)
        ((ibb_integrable hP (ibb_mul hIb hIb) φ).norm.const_mul (ε ^ 2) |>.congr
          (Filter.Eventually.of_forall fun t => by simp [sq]))
      refine Filter.Eventually.of_forall fun t => ?_
      simp only [k, Pi.sub_apply, Pi.mul_apply, Pi.smul_apply, smul_eq_mul]
      by_cases ht : t ∈ Ω
      · rw [Set.indicator_of_mem ht, Pi.one_apply, mul_one, mul_one, norm_one, one_pow,
          mul_one, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, sq_abs]
        have := ht.1; have := ht.2
        nlinarith
      · simp [Set.indicator_of_notMem ht]
    rw [integral_const_mul, ← h2] at h3
    rw [← h1] at h3
    have : ‖boundedSpectralIntegral P (k - (x : ℂ) • Ω.indicator 1) φ‖ ^ 2 ≤ (ε * ‖ψ‖) ^ 2 := by
      rw [mul_pow]; exact h3
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 this
  have hψR := hR1 ⟨ψ, hmem⟩
  simp only [uInt_apply] at hψR
  have hψpos : 0 < ‖ψ‖ := norm_pos_iff.2 hφ
  have : ‖ψ‖ ≤ ‖R‖ * (ε * ‖ψ‖) := by
    calc ‖ψ‖ = ‖R (ulim P (fun t : ℝ => (t : ℂ)) ψ - (x : ℂ) • ψ)‖ := by rw [hψR]
      _ ≤ ‖R‖ * ‖ulim P (fun t : ℝ => (t : ℂ)) ψ - (x : ℂ) • ψ‖ := R.le_opNorm _
      _ ≤ ‖R‖ * (ε * ‖ψ‖) := by gcongr
  have hRε : ‖R‖ * ε < 1 := by
    simp only [ε]
    rw [mul_one_div, div_lt_one (by positivity)]
    linarith
  nlinarith

end TeschlQM.Spectral.BFC

namespace TeschlQM.Spectral.BFC

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {P : Set ℝ → (H →L[ℂ] H)}

open TeschlQM.Shared TeschlQM.Spectral

/-- The (real) support set of `P`. -/
def suppSet (P : Set ℝ → (H →L[ℂ] H)) : Set ℝ :=
  {x : ℝ | ∀ ε : ℝ, 0 < ε → P (Set.Ioo (x - ε) (x + ε)) ≠ 0}

lemma spectrum_uInt (hP : IsProjValuedMeasure P) :
    TeschlQM.Spectral.spectrum (uInt hP measurable_id') = (fun x : ℝ => (x : ℂ)) '' suppSet P := by
  ext z
  simp only [TeschlQM.Spectral.spectrum, Set.mem_compl_iff, Set.mem_image]
  constructor
  · intro hz
    by_contra hcon
    apply hz
    by_cases him : z.im = 0
    · have hzr : z = (z.re : ℂ) := by apply Complex.ext <;> simp [him]
      obtain ⟨r, rfl⟩ : ∃ r : ℝ, z = r := ⟨z.re, hzr⟩
      have hnot : r ∉ suppSet P := fun h => hcon ⟨r, h, rfl⟩
      simp only [suppSet, Set.mem_setOf_eq, not_forall, not_not] at hnot
      obtain ⟨ε, hε, hP0⟩ := hnot
      apply resolvent_of_gap hP hε
      have : {x : ℝ | ‖(x : ℂ) - (r : ℂ)‖ < ε} = Set.Ioo (r - ε) (r + ε) := by
        ext x
        simp only [Set.mem_setOf_eq, Set.mem_Ioo, ← Complex.ofReal_sub, Complex.norm_real,
          Real.norm_eq_abs, abs_lt]
        constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith
      rw [this, hP0]
    · apply resolvent_of_gap hP (δ := |z.im|) (abs_pos.2 him)
      have : {x : ℝ | ‖(x : ℂ) - z‖ < |z.im|} = ∅ := by
        ext x
        simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_lt]
        have := Complex.abs_im_le_norm ((x : ℂ) - z)
        simpa using this
      rw [this, pvm_empty hP]
  · rintro ⟨x, hx, rfl⟩
    exact not_resolvent_of_support hP hx

lemma pvm_zero_of_subset (hP : IsProjValuedMeasure P) {A B : Set ℝ} (hA : MeasurableSet A)
    (hB : MeasurableSet B) (hAB : A ⊆ B) (h : P B = 0) : P A = 0 := by
  rw [← Set.inter_eq_left.2 hAB, pvm_inter hP hA hB, h, mul_zero]

lemma isOpen_compl_suppSet (hP : IsProjValuedMeasure P) : IsOpen (suppSet P)ᶜ := by
  rw [isOpen_iff_forall_mem_open]
  intro x hx
  simp only [suppSet, Set.mem_compl_iff, Set.mem_setOf_eq, not_forall, not_not] at hx
  obtain ⟨ε, hε, h0⟩ := hx
  refine ⟨Set.Ioo (x - ε) (x + ε), fun y hy => ?_, isOpen_Ioo, ⟨by linarith, by linarith⟩⟩
  simp only [suppSet, Set.mem_compl_iff, Set.mem_setOf_eq, not_forall, not_not]
  obtain ⟨hy1, hy2⟩ := hy
  refine ⟨min (y - (x - ε)) ((x + ε) - y), lt_min (by linarith) (by linarith), ?_⟩
  apply pvm_zero_of_subset hP measurableSet_Ioo measurableSet_Ioo _ h0
  intro t ht
  have := min_le_left (y - (x - ε)) ((x + ε) - y)
  have := min_le_right (y - (x - ε)) ((x + ε) - y)
  obtain ⟨ht1, ht2⟩ := ht
  constructor <;> linarith

lemma measurableSet_suppSet (hP : IsProjValuedMeasure P) : MeasurableSet (suppSet P) :=
  (isOpen_compl_suppSet hP).measurableSet.of_compl

lemma pvm_compl_suppSet (hP : IsProjValuedMeasure P) : P (suppSet P)ᶜ = 0 := by
  ext ψ
  have hm := (measurableSet_suppSet hP).compl
  have h0 : spectralMeasure P ψ (suppSet P)ᶜ = 0 := by
    apply measure_null_of_locally_null
    intro x hx
    simp only [suppSet, Set.mem_compl_iff, Set.mem_setOf_eq, not_forall, not_not] at hx
    obtain ⟨ε, hε, h0⟩ := hx
    refine ⟨Set.Ioo (x - ε) (x + ε),
      mem_nhdsWithin_of_mem_nhds (Ioo_mem_nhds (by linarith) (by linarith)), ?_⟩
    rw [spectralMeasure_apply hP ψ measurableSet_Ioo, h0]
    simp
  rw [spectralMeasure_apply hP ψ hm] at h0
  simpa using h0

end TeschlQM.Spectral.BFC

namespace TeschlQM.Spectral

open TeschlQM.Spectral.BFC

/-- Teschl, p. 97, Theorem 3.8. -/
theorem spectrum_eq {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (A : H →ₗ.[ℂ] H) (hA : IsSelfAdjoint A) (P : Set ℝ → (H →L[ℂ] H))
    (hP : TeschlQM.Shared.IsProjValuedMeasure P) (hAP : A = spectralIntegral P (fun x => (x : ℂ))) :
    spectrum A =
      (fun x : ℝ => (x : ℂ)) ''
        {x : ℝ | ∀ ε : ℝ, 0 < ε → P (Set.Ioo (x - ε) (x + ε)) ≠ 0} := by
  rw [hAP, spectralIntegral_eq_uInt hP measurable_id']
  exact spectrum_uInt hP

end TeschlQM.Spectral


open MeasureTheory
open scoped ENNReal InnerProductSpace

open TeschlQM.Spectral TeschlQM.Spectral.BFC

/-- Teschl, p. 97, Corollary 3.9. -/
theorem solution {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (A : H →ₗ.[ℂ] H) (hA : IsSelfAdjoint A) (P : Set ℝ → (H →L[ℂ] H))
    (hP : TeschlQM.Shared.IsProjValuedMeasure P) (hAP : A = spectralIntegral P (fun x => (x : ℂ))) :
    P {x : ℝ | (x : ℂ) ∈ spectrum A} = 1 ∧
      P {x : ℝ | (x : ℂ) ∈ resolventSet A} = 0 := by
  have hσ : {x : ℝ | (x : ℂ) ∈ spectrum A} = suppSet P := by
    ext x
    rw [Set.mem_setOf_eq, spectrum_eq A hA P hP hAP]
    constructor
    · rintro ⟨y, hy, hyx⟩
      have : y = x := Complex.ofReal_injective hyx
      rw [← this]; exact hy
    · intro hx; exact ⟨x, hx, rfl⟩
  have hρ : {x : ℝ | (x : ℂ) ∈ resolventSet A} = (suppSet P)ᶜ := by
    rw [← hσ]
    ext x
    simp [TeschlQM.Spectral.spectrum]
  have h0 : P (suppSet P)ᶜ = 0 := pvm_compl_suppSet hP
  refine ⟨?_, by rw [hρ, h0]⟩
  rw [hσ]
  have hm := measurableSet_suppSet hP
  have := pvm_union hP hm hm.compl disjoint_compl_right
  rw [Set.union_compl_self, hP.2.1, h0, add_zero] at this
  exact this.symm

