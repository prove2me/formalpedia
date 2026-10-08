-- Prove2me | solution 1 for TeschlQM.Spectral.spectral_theorem
-- status  : ACCEPTED   (prove)
-- author  : @Gabewhigham
-- created : 2026-10-04T17:40:35.429873+00:00
-- url     : https://prove2.me/submissions/c6247e7f-8ec9-4f36-b184-e109a90c7453

import Mathlib
import Definitions.Def_TeschlQM_Shared_IsProjValuedMeasure
import Definitions.Def_TeschlQM_Spectral_spectralMeasure
import Definitions.Def_TeschlQM_Spectral_boundedSpectralIntegral
import Definitions.Def_TeschlQM_Spectral_spectralIntegral
import Definitions.Def_TeschlQM_Spectral_IsNormalOperator
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

lemma truncSet_star (f : ℝ → ℂ) (n : ℕ) : truncSet (star f) n = truncSet f n := by
  ext x; simp [truncSet]

lemma trunc_star (f : ℝ → ℂ) (n : ℕ) : trunc (star f) n = star (trunc f n) := by
  funext x
  simp only [trunc, truncSet_star, Pi.star_apply]
  by_cases hx : x ∈ truncSet f n
  · simp [Set.indicator_of_mem hx]
  · simp [Set.indicator_of_notMem hx]

lemma spectralDomain_star (f : ℝ → ℂ) : spectralDomain P (star f) = spectralDomain P f := by
  ext ψ; simp [spectralDomain]

lemma domSub_star (hP : IsProjValuedMeasure P) (f : ℝ → ℂ) :
    domSub hP (star f) = domSub hP f :=
  SetLike.coe_injective (spectralDomain_star f)

lemma measurable_star' {f : ℝ → ℂ} (hf : Measurable f) : Measurable (star f) :=
  Complex.continuous_conj.measurable.comp hf

lemma uInt_formalAdjoint (hP : IsProjValuedMeasure P) {f : ℝ → ℂ} (hf : Measurable f) :
    (uInt hP hf).IsFormalAdjoint (uInt hP (measurable_star' hf)) := by
  intro x y
  rw [uInt_apply, uInt_apply]
  have h1 : Filter.Tendsto (fun n => ⟪boundedSpectralIntegral P (trunc f n) x, (y : H)⟫_ℂ)
      Filter.atTop (nhds ⟪ulim P f x, (y : H)⟫_ℂ) :=
    Filter.Tendsto.inner (tendsto_ulim hP hf x.2) tendsto_const_nhds
  have h2 : Filter.Tendsto (fun n => ⟪boundedSpectralIntegral P (trunc f n) x, (y : H)⟫_ℂ)
      Filter.atTop (nhds ⟪(x : H), ulim P (star f) y⟫_ℂ) := by
    have : ∀ n, ⟪boundedSpectralIntegral P (trunc f n) x, (y : H)⟫_ℂ =
        ⟪(x : H), boundedSpectralIntegral P (trunc (star f) n) y⟫_ℂ := by
      intro n
      rw [trunc_star, bsi_star hP (ibb_trunc hf n), ContinuousLinearMap.adjoint_inner_right]
    simp_rw [this]
    exact Filter.Tendsto.inner tendsto_const_nhds
      (tendsto_ulim hP (measurable_star' hf) y.2)
  exact tendsto_nhds_unique h1 h2

lemma trunc_mul_indicator {f : ℝ → ℂ} {n m : ℕ} (hnm : n ≤ m) :
    trunc f m * (truncSet f n).indicator 1 = trunc f n := by
  funext x
  simp only [Pi.mul_apply, trunc]
  by_cases hx : x ∈ truncSet f n
  · have hx' : x ∈ truncSet f m := show ‖f x‖ ≤ (m : ℝ) from
      (show ‖f x‖ ≤ (n : ℝ) from hx).trans (by exact_mod_cast hnm)
    simp [Set.indicator_of_mem hx, Set.indicator_of_mem hx']
  · simp [Set.indicator_of_notMem hx]

lemma ulim_proj_truncSet (hP : IsProjValuedMeasure P) {f : ℝ → ℂ} (hf : Measurable f)
    (n : ℕ) (ψ : H) :
    ulim P f (P (truncSet f n) ψ) = boundedSpectralIntegral P (trunc f n) ψ := by
  have h := tendsto_ulim hP hf (proj_truncSet_mem hP hf n ψ)
  refine tendsto_nhds_unique h (tendsto_const_nhds.congr' ?_)
  filter_upwards [Filter.eventually_ge_atTop n] with m hm
  rw [← bsi_indicator hP (measurableSet_truncSet hf n), ← ContinuousLinearMap.mul_apply,
    ← bsi_mul hP (ibb_trunc hf m) (isBoundedBorel_indicator (measurableSet_truncSet hf n)),
    trunc_mul_indicator hm]

lemma norm_proj_le (hP : IsProjValuedMeasure P) {Ω : Set ℝ} (hΩ : MeasurableSet Ω) (w : H) :
    ‖P Ω w‖ ^ 2 ≤ ‖w‖ ^ 2 := by
  haveI := spectralMeasure_finite hP w
  rw [← spectralMeasure_real hP w hΩ, ← spectralMeasure_univ hP w]
  exact measureReal_mono (Set.subset_univ _)

lemma adjoint_domain_le (hP : IsProjValuedMeasure P) {f : ℝ → ℂ} (hf : Measurable f) :
    (uInt hP hf).adjoint.domain ≤ domSub hP f := by
  intro φ hφ
  set w := (uInt hP hf).adjoint ⟨φ, hφ⟩
  have hdense : Dense ((uInt hP hf).domain : Set H) := dense_spectralDomain hP hf
  have key : ∀ n, P (truncSet f n) w = boundedSpectralIntegral P (trunc (star f) n) φ := by
    intro n
    apply ext_inner_right ℂ
    intro ψ
    have hmem : P (truncSet f n) ψ ∈ (uInt hP hf).domain := proj_truncSet_mem hP hf n ψ
    have hfa := LinearPMap.adjoint_isFormalAdjoint hdense ⟨φ, hφ⟩ ⟨_, hmem⟩
    rw [← pvm_adjoint hP (measurableSet_truncSet hf n), ContinuousLinearMap.adjoint_inner_left]
    change ⟪w, P (truncSet f n) ψ⟫_ℂ = _
    rw [hfa, uInt_apply]
    simp only
    rw [ulim_proj_truncSet hP hf n ψ, trunc_star, bsi_star hP (ibb_trunc hf n),
      ContinuousLinearMap.adjoint_inner_left]
  have hbound : ∀ n, ∫ x, ‖trunc f n x‖ ^ 2 ∂spectralMeasure P φ ≤ ‖w‖ ^ 2 := by
    intro n
    have := bsi_norm_sq hP (ibb_trunc (measurable_star' hf) n) φ
    rw [← key n, trunc_star] at this
    simp only [Pi.star_apply, norm_star] at this
    rw [← this]
    exact norm_proj_le hP (measurableSet_truncSet hf n) w
  show ∫⁻ x, (‖f x‖₊ : ℝ≥0∞) ^ 2 ∂spectralMeasure P φ < ∞
  have hsup : ∀ x, (‖f x‖₊ : ℝ≥0∞) ^ 2 = ⨆ n, (‖trunc f n x‖₊ : ℝ≥0∞) ^ 2 := by
    intro x
    apply le_antisymm
    · obtain ⟨N, hN⟩ := (trunc_eventually f x).exists_forall_of_atTop
      exact le_iSup_of_le N (by rw [hN N le_rfl])
    · exact iSup_le fun n => by
        gcongr
        exact_mod_cast norm_trunc_le f n x
  have hmono : Monotone (fun n x => (‖trunc f n x‖₊ : ℝ≥0∞) ^ 2) := by
    intro n m hnm x
    simp only
    gcongr
    simp only [trunc]
    by_cases hx : x ∈ truncSet f n
    · have hx' : x ∈ truncSet f m := show ‖f x‖ ≤ (m : ℝ) from
        (show ‖f x‖ ≤ (n : ℝ) from hx).trans (by exact_mod_cast hnm)
      rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx']
    · rw [Set.indicator_of_notMem hx]; simp
  simp_rw [hsup]
  rw [lintegral_iSup (fun n => ((ibb_trunc hf n).1.nnnorm.coe_nnreal_ennreal.pow_const 2)) hmono]
  haveI := spectralMeasure_finite hP φ
  refine lt_of_le_of_lt (iSup_le fun n => ?_) (ENNReal.ofReal_lt_top (r := ‖w‖ ^ 2))
  have hint : Integrable (fun x => ‖trunc f n x‖ ^ 2) (spectralMeasure P φ) := by
    obtain ⟨C, hC⟩ := (ibb_trunc hf n).2
    exact Integrable.of_bound ((ibb_trunc hf n).1.norm.pow_const 2).aestronglyMeasurable (C ^ 2)
      (Filter.Eventually.of_forall fun x => by
        rw [Real.norm_of_nonneg (by positivity)]
        exact pow_le_pow_left₀ (norm_nonneg _) (hC x) 2)
  calc ∫⁻ x, (‖trunc f n x‖₊ : ℝ≥0∞) ^ 2 ∂spectralMeasure P φ
      = ENNReal.ofReal (∫ x, ‖trunc f n x‖ ^ 2 ∂spectralMeasure P φ) := by
        rw [ofReal_integral_eq_lintegral_ofReal hint
          (Filter.Eventually.of_forall fun x => by positivity)]
        congr 1; funext x
        rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm_eq_enorm]; rfl
    _ ≤ ENNReal.ofReal (‖w‖ ^ 2) := ENNReal.ofReal_le_ofReal (hbound n)

lemma uInt_adjoint (hP : IsProjValuedMeasure P) {f : ℝ → ℂ} (hf : Measurable f) :
    (uInt hP hf).adjoint = uInt hP (measurable_star' hf) := by
  have hle : uInt hP (measurable_star' hf) ≤ (uInt hP hf).adjoint :=
    LinearPMap.IsFormalAdjoint.le_adjoint (dense_spectralDomain hP hf) (uInt_formalAdjoint hP hf)
  refine (LinearPMap.eq_of_le_of_domain_eq hle (le_antisymm hle.1 ?_)).symm
  show _ ≤ domSub hP (star f)
  rw [domSub_star]
  exact adjoint_domain_le hP hf

end TeschlQM.Spectral.BFC

namespace TeschlQM.Spectral

open TeschlQM.Spectral.BFC

/-- Teschl, p. 92, Theorem 3.2. -/
theorem spectralIntegral_normal {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (P : Set ℝ → (H →L[ℂ] H)) (hP : TeschlQM.Shared.IsProjValuedMeasure P) (f : ℝ → ℂ) (hf : Measurable f) :
    IsSpectralIntegral P f (spectralIntegral P f) ∧
    IsNormalOperator (spectralIntegral P f) ∧
    (spectralIntegral P f).adjoint = spectralIntegral P (star f) := by
  rw [spectralIntegral_eq_uInt hP hf, spectralIntegral_eq_uInt hP (measurable_star' hf)]
  refine ⟨isSpectralIntegral_uInt hP hf, ⟨dense_spectralDomain hP hf, ?_, ?_⟩, uInt_adjoint hP hf⟩
  · rw [uInt_adjoint hP hf]; exact domSub_star hP f
  · intro ψ ψ' h
    have hmem : (ψ' : H) ∈ (uInt hP (measurable_star' hf)).domain := by
      have hdomeq : (uInt hP hf).adjoint.domain = (uInt hP (measurable_star' hf)).domain :=
        congrArg LinearPMap.domain (uInt_adjoint hP hf)
      exact hdomeq ▸ ψ'.2
    have e : (uInt hP hf).adjoint ψ' = uInt hP (measurable_star' hf) ⟨ψ', hmem⟩ :=
      (le_of_eq (uInt_adjoint hP hf)).2 rfl
    rw [e, uInt_apply, uInt_apply]
    simp only
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1
    rw [norm_ulim_sq hP hf ψ.2, norm_ulim_sq hP (measurable_star' hf) hmem, ← h]
    simp

end TeschlQM.Spectral


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


open scoped InnerProductSpace ComplexConjugate

namespace TeschlQM.Spectral.Cay

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {A : H →ₗ.[ℂ] H}

lemma sa_symm (hA : IsSelfAdjoint A) (x y : A.domain) :
    ⟪A x, (y : H)⟫_ℂ = ⟪(x : H), A y⟫_ℂ := by
  have h : A.adjoint.IsFormalAdjoint A := LinearPMap.adjoint_isFormalAdjoint hA.dense_domain
  rw [LinearPMap.isSelfAdjoint_def.mp hA] at h
  exact h x y

lemma sa_mem_of (hA : IsSelfAdjoint A) {v w : H}
    (h : ∀ x : A.domain, ⟪w, (x : H)⟫_ℂ = ⟪v, A x⟫_ℂ) :
    ∃ y : A.domain, (y : H) = v ∧ A y = w := by
  have hv : v ∈ A.adjoint.domain := LinearPMap.mem_adjoint_domain_of_exists v ⟨w, h⟩
  have hw : A.adjoint ⟨v, hv⟩ = w := LinearPMap.adjoint_apply_eq hA.dense_domain _ h
  have hg : (v, w) ∈ A.adjoint.graph := (LinearPMap.mem_graph_iff _).2 ⟨⟨v, hv⟩, rfl, hw⟩
  rw [LinearPMap.isSelfAdjoint_def.mp hA] at hg
  exact (LinearPMap.mem_graph_iff _).1 hg

lemma inner_self_im (hA : IsSelfAdjoint A) (x : A.domain) : (⟪(x : H), A x⟫_ℂ).im = 0 := by
  have h1 := sa_symm hA x x
  have h2 := inner_conj_symm (𝕜 := ℂ) (A x) (x : H)
  rw [h1] at h2
  have := congrArg Complex.im h2
  rw [Complex.conj_im] at this
  linarith

lemma inner_self_im' (hA : IsSelfAdjoint A) (x : A.domain) : (⟪A x, (x : H)⟫_ℂ).im = 0 := by
  rw [sa_symm hA]; exact inner_self_im hA x

lemma norm_le_of_im (hA : IsSelfAdjoint A) (z : ℂ) (x : A.domain) :
    |z.im| * ‖(x : H)‖ ≤ ‖A x - z • (x : H)‖ := by
  have him : (⟪(x : H), A x - z • (x : H)⟫_ℂ).im = -(z.im * ‖(x : H)‖ ^ 2) := by
    rw [inner_sub_right, inner_smul_right, inner_self_eq_norm_sq_to_K]
    simp [inner_self_im hA x]
    norm_cast
    simp
  have h1 : |z.im| * ‖(x : H)‖ ^ 2 ≤ ‖(x : H)‖ * ‖A x - z • (x : H)‖ := by
    calc |z.im| * ‖(x : H)‖ ^ 2 = |(⟪(x : H), A x - z • (x : H)⟫_ℂ).im| := by
          rw [him, abs_neg, abs_mul, abs_sq]
      _ ≤ ‖⟪(x : H), A x - z • (x : H)⟫_ℂ‖ := Complex.abs_im_le_norm _
      _ ≤ _ := norm_inner_le_norm _ _
  rcases (norm_nonneg (x : H)).eq_or_lt with h0 | hpos
  · rw [← h0, mul_zero]; exact norm_nonneg _
  · have : |z.im| * ‖(x : H)‖ * ‖(x : H)‖ ≤ ‖A x - z • (x : H)‖ * ‖(x : H)‖ := by
      nlinarith
    exact le_of_mul_le_mul_right this hpos

lemma norm_add_I_sq (hA : IsSelfAdjoint A) (x : A.domain) :
    ‖A x + Complex.I • (x : H)‖ = ‖A x - Complex.I • (x : H)‖ := by
  have hre : (⟪A x, Complex.I • (x : H)⟫_ℂ).re = 0 := by
    rw [inner_smul_right]
    simp [inner_self_im' hA x]
  have e1 := @norm_add_sq ℂ H _ _ _ (A x) (Complex.I • (x : H))
  have e2 := @norm_sub_sq ℂ H _ _ _ (A x) (Complex.I • (x : H))
  simp only [RCLike.re_to_complex] at e1 e2
  rw [hre] at e1 e2
  have : ‖A x + Complex.I • (x : H)‖ ^ 2 = ‖A x - Complex.I • (x : H)‖ ^ 2 := by
    rw [e1, e2]; ring
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 this

/-- The linear map `x ↦ A x - z x` on the domain of `A`. -/
noncomputable def subZ (A : H →ₗ.[ℂ] H) (z : ℂ) : A.domain →ₗ[ℂ] H :=
  A.toFun - z • A.domain.subtype

omit [CompleteSpace H] in
@[simp] lemma subZ_apply (z : ℂ) (x : A.domain) : subZ A z x = A x - z • (x : H) := rfl

lemma isClosed_range_subZ (hA : IsSelfAdjoint A) {z : ℂ} (hz : z.im ≠ 0) :
    IsClosed ((LinearMap.range (subZ A z) : Submodule ℂ H) : Set H) := by
  refine isSeqClosed_iff_isClosed.mp ?_
  intro u φ hu hlim
  choose x hx using hu
  have hc : 0 < |z.im| := abs_pos.2 hz
  have hbd : ∀ n m, ‖(x n : H) - x m‖ ≤ |z.im|⁻¹ * ‖u n - u m‖ := by
    intro n m
    have h := norm_le_of_im hA z (x n - x m)
    have e : A (x n - x m) - z • ((x n - x m : A.domain) : H) = u n - u m := by
      rw [← hx n, ← hx m, subZ_apply, subZ_apply, LinearPMap.map_sub]
      simp only [Submodule.coe_sub, smul_sub]; abel
    rw [e, Submodule.coe_sub] at h
    rw [le_inv_mul_iff₀ hc]; exact h
  have hxc : CauchySeq (fun n => (x n : H)) := by
    rw [Metric.cauchySeq_iff']
    intro ε hε
    obtain ⟨N, hN⟩ := Metric.cauchySeq_iff'.1 hlim.cauchySeq (ε * |z.im|) (by positivity)
    refine ⟨N, fun n hn => ?_⟩
    rw [dist_eq_norm]
    calc ‖(x n : H) - x N‖ ≤ |z.im|⁻¹ * ‖u n - u N‖ := hbd n N
      _ < |z.im|⁻¹ * (ε * |z.im|) := by
          apply mul_lt_mul_of_pos_left _ (inv_pos.2 hc)
          rw [← dist_eq_norm]; exact hN n hn
      _ = ε := by field_simp
  obtain ⟨ψ, hψ⟩ := cauchySeq_tendsto_of_complete hxc
  have hAx : Filter.Tendsto (fun n => A (x n)) Filter.atTop (nhds (φ + z • ψ)) := by
    have : (fun n => A (x n)) = fun n => u n + z • (x n : H) := by
      funext n; rw [← hx n, subZ_apply]; abel
    rw [this]; exact hlim.add (hψ.const_smul z)
  have hg : (ψ, φ + z • ψ) ∈ A.graph := by
    have hcl := hA.isClosed
    refine hcl.mem_of_tendsto (hψ.prodMk_nhds hAx) (Filter.Eventually.of_forall fun n => ?_)
    exact (LinearPMap.mem_graph_iff _).2 ⟨x n, rfl, rfl⟩
  obtain ⟨y, hy1, hy2⟩ := (LinearPMap.mem_graph_iff _).1 hg
  refine ⟨y, ?_⟩
  simp only [subZ_apply]
  rw [hy2, hy1]; simp

lemma orth_range_subZ (hA : IsSelfAdjoint A) {z : ℂ} (hz : z.im ≠ 0) :
    (LinearMap.range (subZ A z))ᗮ = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro v hv
  have h0 : ∀ x : A.domain, ⟪v, A x - z • (x : H)⟫_ℂ = 0 := fun x =>
    (Submodule.mem_orthogonal' _ _).1 hv _ ⟨x, rfl⟩
  obtain ⟨y, hy1, hy2⟩ := sa_mem_of hA (v := v) (w := conj z • v) (fun x => by
    have := h0 x
    rw [inner_sub_right, inner_smul_right, sub_eq_zero] at this
    rw [inner_smul_left, Complex.conj_conj, this])
  have him := inner_self_im hA y
  rw [hy2, hy1, inner_smul_right, inner_self_eq_norm_sq_to_K] at him
  have : z.im * ‖v‖ ^ 2 = 0 := by
    have e : ((conj z) * ((‖v‖ : ℂ) ^ 2)).im = -(z.im * ‖v‖ ^ 2) := by
      rw [← Complex.ofReal_pow, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]; simp
    have := e.symm.trans him
    linarith
  have := (mul_eq_zero.1 this).resolve_left hz
  exact norm_eq_zero.1 (pow_eq_zero_iff (two_ne_zero) |>.1 this)

lemma surj_sub (hA : IsSelfAdjoint A) {z : ℂ} (hz : z.im ≠ 0) (φ : H) :
    ∃ x : A.domain, A x - z • (x : H) = φ := by
  have hK := isClosed_range_subZ hA hz
  haveI : CompleteSpace (LinearMap.range (subZ A z)) := hK.completeSpace_coe
  have htop := (Submodule.orthogonal_eq_bot_iff).1 (orth_range_subZ hA hz)
  have : φ ∈ LinearMap.range (subZ A z) := by rw [htop]; trivial
  obtain ⟨x, hx⟩ := this
  exact ⟨x, hx⟩

/-- The Cayley transform of a self-adjoint operator. -/
theorem exists_cayley (hA : IsSelfAdjoint A) :
    ∃ U : H →L[ℂ] H, U ∈ unitary (H →L[ℂ] H) ∧
      (∀ x : A.domain, U (A x + Complex.I • (x : H)) = A x - Complex.I • (x : H)) ∧
      ∀ φ : H, ∃ x : A.domain, A x + Complex.I • (x : H) = φ := by
  have hL : ∀ x : A.domain, subZ A (-Complex.I) x = A x + Complex.I • (x : H) := by
    intro x; simp [sub_eq_add_neg]
  have hinj : Function.Injective (subZ A (-Complex.I)) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    have h := norm_le_of_im hA (-Complex.I) x
    rw [← subZ_apply, hx] at h
    simp at h
    exact Subtype.ext (by simpa using h)
  have hsurj : Function.Surjective (subZ A (-Complex.I)) := fun φ =>
    surj_sub hA (z := -Complex.I) (by simp) φ
  set e := LinearEquiv.ofBijective (subZ A (-Complex.I)) ⟨hinj, hsurj⟩ with he
  have he1 : ∀ x : A.domain, e.symm (A x + Complex.I • (x : H)) = x := by
    intro x; rw [← hL]; exact e.symm_apply_apply x
  have he2 : ∀ φ, A (e.symm φ) + Complex.I • ((e.symm φ : A.domain) : H) = φ := by
    intro φ; rw [← hL]; exact e.apply_symm_apply φ
  let Ul : H →ₗ[ℂ] H := subZ A Complex.I ∘ₗ e.symm.toLinearMap
  have hUl : ∀ φ, Ul φ = A (e.symm φ) - Complex.I • ((e.symm φ : A.domain) : H) := fun φ => rfl
  have hnorm : ∀ φ, ‖Ul φ‖ = ‖φ‖ := by
    intro φ
    rw [hUl]
    conv_rhs => rw [← he2 φ]
    exact (norm_add_I_sq hA _).symm
  let Ui : H →ₗᵢ[ℂ] H := ⟨Ul, hnorm⟩
  have hUsurj : Function.Surjective Ui := by
    intro χ
    obtain ⟨x, hx⟩ := surj_sub hA (z := Complex.I) (by simp) χ
    refine ⟨A x + Complex.I • (x : H), ?_⟩
    change Ul _ = χ
    rw [hUl, he1]; exact hx
  let eU := LinearIsometryEquiv.ofSurjective Ui hUsurj
  refine ⟨(Unitary.linearIsometryEquiv.symm eU : H →L[ℂ] H),
    (Unitary.linearIsometryEquiv.symm eU).property, ?_, ?_⟩
  · intro x
    rw [Unitary.coe_symm_linearIsometryEquiv_apply]
    change Ul _ = _
    rw [hUl, he1]
  · intro φ
    exact ⟨e.symm φ, he2 φ⟩

end TeschlQM.Spectral.Cay


open Filter Topology
open scoped InnerProductSpace ComplexConjugate

namespace TeschlQM.Spectral.Circ

/-! ### The Cayley map between `ℝ` and the unit circle -/

/-- Inverse Cayley map from the unit circle minus `1` to `ℝ`. -/
noncomputable def cay (z : ℂ) : ℝ := -z.im / (1 - z.re)

/-- Cayley map `ℝ → S¹ \ {1}`, `x ↦ (x - i)/(x + i)`. -/
noncomputable def kap (x : ℝ) : ℂ := ((x : ℂ) - Complex.I) / ((x : ℂ) + Complex.I)

/-- Transport of a function on `ℝ` to the circle, with value `0` at `1`. -/
noncomputable def lift (f : ℝ → ℂ) (z : ℂ) : ℂ := if z = 1 then 0 else f (cay z)

lemma add_I_ne_zero (x : ℝ) : (x : ℂ) + Complex.I ≠ 0 := by
  intro h; have := congrArg Complex.im h; simp at this

lemma kap_re (x : ℝ) : (kap x).re = (x ^ 2 - 1) / (x ^ 2 + 1) := by
  simp [kap, Complex.div_re, Complex.normSq_apply]
  field_simp
  ring

lemma kap_im (x : ℝ) : (kap x).im = -2 * x / (x ^ 2 + 1) := by
  simp [kap, Complex.div_im, Complex.normSq_apply]
  field_simp
  ring

lemma norm_kap (x : ℝ) : ‖kap x‖ = 1 := by
  have h : ‖kap x‖ ^ 2 = 1 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, kap_re, kap_im]
    field_simp
    ring
  nlinarith [norm_nonneg (kap x)]

lemma kap_ne_one (x : ℝ) : kap x ≠ 1 := by
  intro h
  have := congrArg Complex.re h
  rw [kap_re, Complex.one_re] at this
  field_simp at this
  linarith

lemma cay_kap (x : ℝ) : cay (kap x) = x := by
  unfold cay
  rw [kap_re, kap_im]
  field_simp
  ring

lemma re_sq_add_im_sq {z : ℂ} (hz : ‖z‖ = 1) : z.re ^ 2 + z.im ^ 2 = 1 := by
  have := Complex.sq_norm z
  rw [hz, Complex.normSq_apply] at this
  nlinarith

lemma re_lt_one {z : ℂ} (hz : ‖z‖ = 1) (h1 : z ≠ 1) : z.re < 1 := by
  have hn := re_sq_add_im_sq hz
  by_contra h
  push_neg at h
  have hre : z.re = 1 := by nlinarith [sq_nonneg z.im]
  have him : z.im = 0 := by nlinarith [sq_nonneg z.im]
  exact h1 (Complex.ext (by simp [hre]) (by simp [him]))

lemma kap_cay {z : ℂ} (hz : ‖z‖ = 1) (h1 : z ≠ 1) : kap (cay z) = z := by
  have hn := re_sq_add_im_sq hz
  have hlt := re_lt_one hz h1
  have hne : 1 - z.re ≠ 0 := by linarith
  apply Complex.ext
  · rw [kap_re]; unfold cay
    field_simp
    nlinarith
  · rw [kap_im]; unfold cay
    field_simp
    linear_combination (-z.im) * hn

lemma norm_one_sub_sq_mul {z : ℂ} (hz : ‖z‖ = 1) (h1 : z ≠ 1) :
    ‖1 - z‖ ^ 2 * (cay z ^ 2 + 1) = 4 := by
  have hn := re_sq_add_im_sq hz
  have hlt := re_lt_one hz h1
  have hne : 1 - z.re ≠ 0 := by linarith
  rw [Complex.sq_norm, Complex.normSq_apply]
  unfold cay
  simp only [Complex.sub_re, Complex.one_re, Complex.sub_im, Complex.one_im]
  field_simp
  nlinarith

lemma norm_one_sub_kap_sq (x : ℝ) : ‖1 - kap x‖ ^ 2 * (x ^ 2 + 1) = 4 := by
  have := norm_one_sub_sq_mul (norm_kap x) (kap_ne_one x)
  rwa [cay_kap] at this

/-- Continuity of the transported function on the circle. -/
lemma continuousOn_lift {f : ℝ → ℂ} (hf : Continuous f) (hs : HasCompactSupport f) :
    ContinuousOn (lift f) (Metric.sphere 0 1) := by
  obtain ⟨R, hR⟩ : ∃ R : ℝ, ∀ x, R < |x| → f x = 0 := by
    obtain ⟨R, hR⟩ := hs.isCompact.isBounded.subset_closedBall 0
    refine ⟨R, fun x hx => ?_⟩
    by_contra h
    have h2 := hR (subset_tsupport f h)
    rw [Metric.mem_closedBall, Real.dist_eq, sub_zero] at h2
    linarith
  intro z hz
  have hz1 : ‖z‖ = 1 := by simpa using hz
  by_cases h1 : z = 1
  · subst h1
    have hval : lift f 1 = 0 := by simp [lift]
    rw [ContinuousWithinAt, hval]
    set δ : ℝ := 2 / (|R| + 1) with hδ
    have hδpos : 0 < δ := by positivity
    have key : ∀ w : ℂ, ‖w‖ = 1 → ‖w - 1‖ < δ → lift f w = 0 := by
      intro w hw hwδ
      by_cases hw1 : w = 1
      · simp [lift, hw1]
      simp only [lift, hw1, if_false]
      apply hR
      have he := norm_one_sub_sq_mul hw hw1
      rw [norm_sub_rev] at hwδ
      set t := ‖1 - w‖
      set c := cay w
      have ht0 : 0 ≤ t := norm_nonneg _
      have hc1 : 0 < c ^ 2 + 1 := by positivity
      have h2 : t ^ 2 < δ ^ 2 := by nlinarith
      have h3 : 4 < δ ^ 2 * (c ^ 2 + 1) := by nlinarith
      have h4 : δ ^ 2 * (|R| + 1) ^ 2 = 4 := by
        rw [hδ]; field_simp; norm_num
      have h5 : (|R| + 1) ^ 2 < c ^ 2 + 1 := by
        by_contra hcon; push_neg at hcon
        have := mul_le_mul_of_nonneg_left hcon (sq_nonneg δ)
        linarith
      have h6 : |R| ^ 2 < |c| ^ 2 := by
        rw [sq_abs c]; nlinarith [abs_nonneg R]
      have h7 : |R| < |c| := by
        exact lt_of_pow_lt_pow_left₀ 2 (abs_nonneg c) h6
      exact (le_abs_self R).trans_lt h7
    refine tendsto_const_nhds.congr' ?_
    have hb : Metric.ball (1 : ℂ) δ ∈ 𝓝 (1 : ℂ) := Metric.ball_mem_nhds 1 hδpos
    filter_upwards [inter_mem_nhdsWithin (Metric.sphere (0 : ℂ) 1) hb, self_mem_nhdsWithin]
      with w hw hws
    have hw1 : ‖w‖ = 1 := by simpa using hws
    exact (key w hw1 (by simpa [dist_eq_norm] using hw.2)).symm
  · have hlt := re_lt_one hz1 h1
    have hcay : ContinuousAt cay z := by
      unfold cay
      refine ContinuousAt.div ?_ ?_ (by linarith)
      · exact (Complex.continuous_im.neg).continuousAt
      · exact (continuous_const.sub Complex.continuous_re).continuousAt
    have hca : ContinuousAt (fun w => f (cay w)) z := hf.continuousAt.comp hcay
    have heq : (fun w => f (cay w)) =ᶠ[𝓝 z] lift f := by
      filter_upwards [isOpen_ne.mem_nhds h1] with w hw
      simp [lift, hw]
    exact (hca.congr heq).continuousWithinAt

end TeschlQM.Spectral.Circ


open Filter Topology
open scoped InnerProductSpace ComplexConjugate

namespace TeschlQM.Spectral.Circ

/-- Continuous compactly supported complex functions on `ℝ`. -/
def IsCc (f : ℝ → ℂ) : Prop := Continuous f ∧ HasCompactSupport f

lemma IsCc.add {f g : ℝ → ℂ} (hf : IsCc f) (hg : IsCc g) : IsCc (f + g) :=
  ⟨hf.1.add hg.1, hf.2.add hg.2⟩

lemma IsCc.smul {f : ℝ → ℂ} (c : ℂ) (hf : IsCc f) : IsCc (c • f) :=
  ⟨hf.1.const_smul c, hf.2.smul_left⟩

lemma IsCc.mul {f g : ℝ → ℂ} (hf : IsCc f) (hg : IsCc g) : IsCc (f * g) :=
  ⟨hf.1.mul hg.1, hf.2.mul_right⟩

lemma IsCc.mul_left {f g : ℝ → ℂ} (hf : Continuous f) (hg : IsCc g) : IsCc (f * g) :=
  ⟨hf.mul hg.1, hg.2.mul_left⟩

lemma IsCc.star {f : ℝ → ℂ} (hf : IsCc f) : IsCc (star f) :=
  ⟨hf.1.star, by
    exact hf.2.comp_left (g := (Star.star : ℂ → ℂ)) (star_zero _)⟩

lemma IsCc.ofReal {g : ℝ → ℝ} (hg : Continuous g) (hs : HasCompactSupport g) :
    IsCc (fun x => (g x : ℂ)) :=
  ⟨Complex.continuous_ofReal.comp hg, hs.comp_left Complex.ofReal_zero⟩

lemma lift_add (f g : ℝ → ℂ) : lift (f + g) = fun z => lift f z + lift g z := by
  funext z; by_cases h : z = 1 <;> simp [lift, h]

lemma lift_smul (c : ℂ) (f : ℝ → ℂ) : lift (c • f) = fun z => c * lift f z := by
  funext z; by_cases h : z = 1 <;> simp [lift, h]

lemma lift_mul (f g : ℝ → ℂ) : lift (f * g) = fun z => lift f z * lift g z := by
  funext z; by_cases h : z = 1 <;> simp [lift, h]

lemma lift_star (f : ℝ → ℂ) : lift (star f) = fun z => star (lift f z) := by
  funext z; by_cases h : z = 1 <;> simp [lift, h]

lemma norm_lift_le {f : ℝ → ℂ} {C : ℝ} (hC : 0 ≤ C) (hf : ∀ x, ‖f x‖ ≤ C) (z : ℂ) :
    ‖lift f z‖ ≤ C := by
  by_cases h : z = 1 <;> simp [lift, h, hC, hf]

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {U : H →L[ℂ] H}

/-- The continuous functional calculus of the unitary `U`, transported to `ℝ`. -/
noncomputable def FC (U : H →L[ℂ] H) (f : ℝ → ℂ) : H →L[ℂ] H := cfc (lift f) U

lemma spec_sub (hU : U ∈ unitary (H →L[ℂ] H)) : _root_.spectrum ℂ U ⊆ Metric.sphere 0 1 :=
  _root_.spectrum.subset_circle_of_unitary hU

lemma contOn (hU : U ∈ unitary (H →L[ℂ] H)) {f : ℝ → ℂ} (hf : IsCc f) :
    ContinuousOn (lift f) (_root_.spectrum ℂ U) :=
  (continuousOn_lift hf.1 hf.2).mono (spec_sub hU)

lemma FC_add (hU : U ∈ unitary (H →L[ℂ] H)) {f g : ℝ → ℂ} (hf : IsCc f) (hg : IsCc g) :
    FC U (f + g) = FC U f + FC U g := by
  unfold FC
  rw [lift_add]
  exact cfc_add (hf := contOn hU hf) (hg := contOn hU hg) ..

lemma FC_smul (hU : U ∈ unitary (H →L[ℂ] H)) (c : ℂ) {f : ℝ → ℂ} (hf : IsCc f) :
    FC U (c • f) = c • FC U f := by
  unfold FC
  rw [lift_smul]
  exact cfc_const_mul (hf := contOn hU hf) ..

lemma FC_mul (hU : U ∈ unitary (H →L[ℂ] H)) {f g : ℝ → ℂ} (hf : IsCc f) (hg : IsCc g) :
    FC U (f * g) = FC U f * FC U g := by
  unfold FC
  rw [lift_mul]
  exact cfc_mul (hf := contOn hU hf) (hg := contOn hU hg) ..

lemma FC_star (f : ℝ → ℂ) : FC U (star f) = star (FC U f) := by
  unfold FC
  rw [lift_star]
  exact cfc_star _ _

lemma FC_norm_le {f : ℝ → ℂ} {C : ℝ} (hC : 0 ≤ C) (hf : ∀ x, ‖f x‖ ≤ C) :
    ‖FC U f‖ ≤ C :=
  norm_cfc_le hC (fun z _ => norm_lift_le hC hf z)

lemma FC_kap_mul (hU : U ∈ unitary (H →L[ℂ] H)) {f : ℝ → ℂ} (hf : IsCc f) :
    FC U (kap * f) = U * FC U f := by
  haveI := isStarNormal_of_mem_unitary hU
  unfold FC
  have heq : (_root_.spectrum ℂ U).EqOn (lift (kap * f)) (fun z => z * lift f z) := by
    intro z hz
    have hz1 : ‖z‖ = 1 := by simpa using spec_sub hU hz
    by_cases h : z = 1
    · simp [lift, h]
    · simp [lift, h, kap_cay hz1 h]
  rw [cfc_congr heq, cfc_mul (fun z => z) _ _ continuousOn_id (contOn hU hf), cfc_id' ℂ U]

lemma FC_real_selfAdjoint {g : ℝ → ℝ} : star (FC U (fun x => (g x : ℂ))) =
    FC U (fun x => (g x : ℂ)) := by
  rw [← FC_star]
  congr 1
  funext x
  simp

lemma FC_inner_nonneg (hU : U ∈ unitary (H →L[ℂ] H)) {g : ℝ → ℝ} (hg : Continuous g)
    (hs : HasCompactSupport g) (h0 : ∀ x, 0 ≤ g x) (ψ : H) :
    ∃ r : ℝ, 0 ≤ r ∧ ⟪ψ, FC U (fun x => (g x : ℂ)) ψ⟫_ℂ = r := by
  set k : ℝ → ℝ := fun x => Real.sqrt (g x)
  have hk : Continuous k := hg.sqrt
  have hks : HasCompactSupport k := hs.comp_left Real.sqrt_zero
  have hkk : (fun x => (g x : ℂ)) = star (fun x => (k x : ℂ)) * (fun x => (k x : ℂ)) := by
    funext x
    simp only [Pi.mul_apply, Pi.star_apply, Complex.star_def, Complex.conj_ofReal]
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (h0 x)]
  rw [hkk, FC_mul hU (IsCc.ofReal hk hks).star (IsCc.ofReal hk hks), FC_star]
  refine ⟨‖FC U (fun x => (k x : ℂ)) ψ‖ ^ 2, sq_nonneg _, ?_⟩
  rw [ContinuousLinearMap.mul_apply, ContinuousLinearMap.star_eq_adjoint,
    ContinuousLinearMap.adjoint_inner_right, inner_self_eq_norm_sq_to_K]
  simp

lemma FC_one_sub (hU : U ∈ unitary (H →L[ℂ] H)) {f : ℝ → ℂ} (hf : IsCc f) :
    (1 - U) - (1 - U) * FC U f = cfc (fun z => (1 - z) * (1 - lift f z)) U := by
  haveI := isStarNormal_of_mem_unitary hU
  unfold FC
  rw [cfc_mul (fun z => 1 - z) (fun z => 1 - lift f z) U (by fun_prop)
    (continuousOn_const.sub (contOn hU hf))]
  rw [cfc_sub (fun _ => (1 : ℂ)) (fun z => z), cfc_sub (fun _ => (1 : ℂ)) (lift f) U continuousOn_const
    (contOn hU hf), cfc_const_one ℂ U, cfc_id' ℂ U]
  noncomm_ring

/-- Norm estimate for `(1 - U)(1 - F(f))` when `f = 1` on `[-n, n]`. -/
lemma FC_approx (hU : U ∈ unitary (H →L[ℂ] H)) {f : ℝ → ℂ} (hf : IsCc f)
    (hb : ∀ x, ‖f x‖ ≤ 1) {n : ℝ} (hn : 0 < n) (h1 : ∀ x, |x| ≤ n → f x = 1) :
    ‖(1 - U) - (1 - U) * FC U f‖ ≤ 4 / n := by
  rw [FC_one_sub hU hf]
  refine norm_cfc_le (by positivity) (fun z hz => ?_)
  have hz1 : ‖z‖ = 1 := by simpa using spec_sub hU hz
  by_cases hz0 : z = 1
  · simp [hz0]; positivity
  rw [norm_mul]
  by_cases hc : |cay z| ≤ n
  · simp [lift, hz0, h1 _ hc]; positivity
  push_neg at hc
  have hl : ‖1 - lift f z‖ ≤ 2 := by
    calc ‖1 - lift f z‖ ≤ ‖(1 : ℂ)‖ + ‖lift f z‖ := norm_sub_le _ _
      _ ≤ 1 + 1 := by rw [norm_one]; gcongr; exact norm_lift_le zero_le_one hb z
      _ = 2 := by norm_num
  have he := norm_one_sub_sq_mul hz1 hz0
  have hzn : ‖1 - z‖ ≤ 2 / n := by
    set t := ‖1 - z‖
    set c := cay z
    have ht0 : 0 ≤ t := norm_nonneg _
    have hc2 : n ^ 2 < c ^ 2 := by
      have := sq_lt_sq' (by linarith [abs_nonneg c, neg_abs_le c]) hc
      rwa [sq_abs] at this
    rw [le_div_iff₀ hn]
    by_contra hcon; push_neg at hcon
    have : 4 < t ^ 2 * (c ^ 2 + 1) := by nlinarith
    linarith
  calc ‖1 - z‖ * ‖1 - lift f z‖ ≤ (2 / n) * 2 :=
        mul_le_mul hzn hl (norm_nonneg _) (by positivity)
    _ = 4 / n := by ring

end TeschlQM.Spectral.Circ


open MeasureTheory Filter Topology
open scoped ENNReal InnerProductSpace ComplexConjugate

namespace TeschlQM.Spectral.BFC

open TeschlQM.Shared TeschlQM.Spectral

/-- A functional on `ℝ → ℂ` which is linear on bounded Borel functions and sequentially
continuous along uniformly bounded pointwise convergence. -/
structure GoodL (L : (ℝ → ℂ) → ℂ) : Prop where
  add : ∀ f g, IsBoundedBorel f → IsBoundedBorel g → L (f + g) = L f + L g
  smul : ∀ (c : ℂ) f, IsBoundedBorel f → L (c • f) = c * L f
  lim : ∀ (fs : ℕ → ℝ → ℂ) (f : ℝ → ℂ) (C : ℝ), (∀ n, IsBoundedBorel (fs n)) →
    IsBoundedBorel f → (∀ n x, ‖fs n x‖ ≤ C) →
    (∀ x, Tendsto (fun n => fs n x) atTop (𝓝 (f x))) →
    Tendsto (fun n => L (fs n)) atTop (𝓝 (L f))

lemma goodL_integral (μ : Measure ℝ) [IsFiniteMeasure μ] : GoodL (fun f => ∫ x, f x ∂μ) where
  add f g hf hg := by
    obtain ⟨C, hC⟩ := hf.2
    obtain ⟨D, hD⟩ := hg.2
    have hfi : Integrable f μ := Integrable.of_bound hf.1.aestronglyMeasurable C
      (Eventually.of_forall hC)
    have hgi : Integrable g μ := Integrable.of_bound hg.1.aestronglyMeasurable D
      (Eventually.of_forall hD)
    exact integral_add hfi hgi
  smul c f _ := by
    simp only [Pi.smul_apply, smul_eq_mul]
    exact integral_const_mul c _
  lim fs f C hfs _ hb hl := by
    refine tendsto_integral_of_dominated_convergence (fun _ => C)
      (fun n => (hfs n).1.aestronglyMeasurable) (integrable_const C)
      (fun n => Eventually.of_forall (hb n)) (Eventually.of_forall hl)

lemma GoodL.zero {L : (ℝ → ℂ) → ℂ} (hL : GoodL L) : L 0 = 0 := by
  have := hL.smul 0 0 (isBoundedBorel_const 0)
  simpa using this

lemma GoodL.add' {L M : (ℝ → ℂ) → ℂ} (hL : GoodL L) (hM : GoodL M) :
    GoodL (fun f => L f + M f) where
  add f g hf hg := by rw [hL.add f g hf hg, hM.add f g hf hg]; ring
  smul c f hf := by rw [hL.smul c f hf, hM.smul c f hf]; ring
  lim fs f C hfs hf hb hl := (hL.lim fs f C hfs hf hb hl).add (hM.lim fs f C hfs hf hb hl)

lemma GoodL.const_mul {L : (ℝ → ℂ) → ℂ} (hL : GoodL L) (a : ℂ) :
    GoodL (fun f => a * L f) where
  add f g hf hg := by rw [hL.add f g hf hg]; ring
  smul c f hf := by rw [hL.smul c f hf]; ring
  lim fs f C hfs hf hb hl := (hL.lim fs f C hfs hf hb hl).const_mul a

lemma GoodL.sub' {L M : (ℝ → ℂ) → ℂ} (hL : GoodL L) (hM : GoodL M) :
    GoodL (fun f => L f - M f) := by
  have := hL.add' (hM.const_mul (-1))
  simpa [sub_eq_add_neg] using this

lemma GoodL.comp_mul {L : (ℝ → ℂ) → ℂ} (hL : GoodL L) {g : ℝ → ℂ} (hg : IsBoundedBorel g) :
    GoodL (fun f => L (g * f)) where
  add f h hf hh := by rw [mul_add]; exact hL.add _ _ (ibb_mul hg hf) (ibb_mul hg hh)
  smul c f hf := by rw [mul_smul_comm]; exact hL.smul _ _ (ibb_mul hg hf)
  lim fs f C hfs hf hb hl := by
    obtain ⟨D, hD⟩ := hg.2
    refine hL.lim _ _ (D * C) (fun n => ibb_mul hg (hfs n)) (ibb_mul hg hf) ?_ ?_
    · intro n x
      rw [Pi.mul_apply, norm_mul]
      exact mul_le_mul (hD x) (hb n x) (norm_nonneg _) ((norm_nonneg _).trans (hD x))
    · intro x; exact (hl x).const_mul (g x)

lemma GoodL.conj {L : (ℝ → ℂ) → ℂ} (hL : GoodL L) :
    GoodL (fun f => starRingEnd ℂ (L (star f))) where
  add f g hf hg := by
    rw [star_add, hL.add _ _ (ibb_star hf) (ibb_star hg), map_add]
  smul c f hf := by
    rw [star_smul, hL.smul _ _ (ibb_star hf), map_mul]
    simp
  lim fs f C hfs hf hb hl := by
    refine (Complex.continuous_conj.tendsto _).comp
      (hL.lim _ _ C (fun n => ibb_star (hfs n)) (ibb_star hf) ?_ ?_)
    · intro n x; simpa using hb n x
    · intro x; exact (Complex.continuous_conj.tendsto _).comp (hl x)

lemma ibb_finset_sum' {ι : Type*} (s : Finset ι) (fs : ι → ℝ → ℂ)
    (hfs : ∀ i, IsBoundedBorel (fs i)) : IsBoundedBorel (∑ i ∈ s, fs i) := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty]; exact isBoundedBorel_const 0
  | insert a s ha ih => rw [Finset.sum_insert ha]; exact ibb_add (hfs a) ih

lemma GoodL.finset_sum {L : (ℝ → ℂ) → ℂ} (hL : GoodL L) {ι : Type*} (s : Finset ι)
    (fs : ι → ℝ → ℂ) (hfs : ∀ i, IsBoundedBorel (fs i)) :
    L (∑ i ∈ s, fs i) = ∑ i ∈ s, L (fs i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using hL.zero
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, hL.add _ _ (hfs a)
      (ibb_finset_sum' s fs hfs), ih]

lemma GoodL.eq_of_lim {L M : (ℝ → ℂ) → ℂ} (hL : GoodL L) (hM : GoodL M)
    (fs : ℕ → ℝ → ℂ) (f : ℝ → ℂ) (C : ℝ) (hfs : ∀ n, IsBoundedBorel (fs n))
    (hf : IsBoundedBorel f) (hb : ∀ n x, ‖fs n x‖ ≤ C)
    (hl : ∀ x, Tendsto (fun n => fs n x) atTop (𝓝 (f x))) (h : ∀ n, L (fs n) = M (fs n)) :
    L f = M f := by
  have t1 := hL.lim fs f C hfs hf hb hl
  have t2 := hM.lim fs f C hfs hf hb hl
  simp only [h] at t1
  exact tendsto_nhds_unique t1 t2

/-- Equality on indicators of Borel sets extends to all bounded Borel functions. -/
lemma GoodL.ext_ind {L M : (ℝ → ℂ) → ℂ} (hL : GoodL L) (hM : GoodL M)
    (h : ∀ Ω, MeasurableSet Ω → L (Ω.indicator 1) = M (Ω.indicator 1)) :
    ∀ f, IsBoundedBorel f → L f = M f := by
  refine isBoundedBorel_induction (fun f => L f = M f) h ?_ ?_ ?_
  · intro f g hf hg h1 h2; rw [hL.add f g hf hg, hM.add f g hf hg, h1, h2]
  · intro c f hf h1; rw [hL.smul c f hf, hM.smul c f hf, h1]
  · intro fs f hfs hQ hf hu
    obtain ⟨C, hC⟩ := hf.2
    obtain ⟨N, hN⟩ := eventually_atTop.1 (Metric.tendstoUniformly_iff.1 hu 1 one_pos)
    have hb : ∀ n x, ‖fs (n + N) x‖ ≤ C + 1 := by
      intro n x
      have h1 := hN (n + N) (by omega) x
      rw [dist_eq_norm] at h1
      have := norm_sub_norm_le (fs (n + N) x) (f x)
      rw [norm_sub_rev] at h1
      linarith [hC x]
    exact hL.eq_of_lim hM _ f (C + 1) (fun n => hfs _) hf hb
      (fun x => (hu.tendsto_at x).comp (tendsto_add_atTop_nat N)) (fun n => hQ _)

lemma ibb_ofReal_of_continuous {g : ℝ → ℝ} (hg : Continuous g) (hb : ∀ x, |g x| ≤ 1) :
    IsBoundedBorel (fun x => (g x : ℂ)) :=
  ⟨(Complex.continuous_ofReal.comp hg).measurable, 1, fun x => by
    rw [Complex.norm_real, Real.norm_eq_abs]; exact hb x⟩

/-- Indicators of open intervals are bounded pointwise limits of continuous compactly
supported functions. -/
lemma GoodL.eq_Ioo {L M : (ℝ → ℂ) → ℂ} (hL : GoodL L) (hM : GoodL M)
    (h : ∀ g : ℝ → ℝ, Continuous g → HasCompactSupport g →
      L (fun x => (g x : ℂ)) = M (fun x => (g x : ℂ))) (a b : ℝ) :
    L ((Set.Ioo a b).indicator 1) = M ((Set.Ioo a b).indicator 1) := by
  let g : ℕ → ℝ → ℝ := fun n x => max 0 (min 1 (n * min (x - a) (b - x)))
  have gc : ∀ n, Continuous (g n) := fun n => by fun_prop
  have gb : ∀ n x, |g n x| ≤ 1 := by
    intro n x
    rw [abs_of_nonneg (le_max_left _ _)]
    exact max_le zero_le_one (min_le_left _ _)
  have gs : ∀ n, HasCompactSupport (g n) := by
    intro n
    refine HasCompactSupport.intro (isCompact_Icc (a := a) (b := b)) (fun x hx => ?_)
    simp only [Set.mem_Icc, not_and_or, not_le] at hx
    have hm : min (x - a) (b - x) ≤ 0 := by
      rcases hx with hx | hx
      · exact (min_le_left _ _).trans (by linarith)
      · exact (min_le_right _ _).trans (by linarith)
    have : (n : ℝ) * min (x - a) (b - x) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg n) hm
    simp only [g]
    exact max_eq_left ((min_le_right _ _).trans this)
  refine hL.eq_of_lim hM (fun n x => (g n x : ℂ)) _ 1
    (fun n => ibb_ofReal_of_continuous (gc n) (gb n))
    (isBoundedBorel_indicator measurableSet_Ioo)
    (fun n x => by rw [Complex.norm_real, Real.norm_eq_abs]; exact gb n x) ?_
    (fun n => h _ (gc n) (gs n))
  intro x
  by_cases hx : x ∈ Set.Ioo a b
  · rw [Set.indicator_of_mem hx]
    have hm : 0 < min (x - a) (b - x) := lt_min (by linarith [hx.1]) (by linarith [hx.2])
    obtain ⟨N, hN⟩ := exists_nat_ge (1 / min (x - a) (b - x))
    refine tendsto_const_nhds.congr' (eventually_atTop.2 ⟨N, fun n hn => ?_⟩)
    have h1 : 1 ≤ (n : ℝ) * min (x - a) (b - x) := by
      have : (N : ℝ) ≤ n := by exact_mod_cast hn
      rw [div_le_iff₀ hm] at hN
      nlinarith
    simp only [g, Pi.one_apply]
    rw [min_eq_left h1, max_eq_right zero_le_one]; simp
  · rw [Set.indicator_of_notMem hx]
    have hm : min (x - a) (b - x) ≤ 0 := by
      simp only [Set.mem_Ioo, not_and_or, not_lt] at hx
      rcases hx with hx | hx
      · exact (min_le_left _ _).trans (by linarith)
      · exact (min_le_right _ _).trans (by linarith)
    refine tendsto_const_nhds.congr' (Eventually.of_forall fun n => ?_)
    have : (n : ℝ) * min (x - a) (b - x) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg n) hm
    simp only [g]
    rw [max_eq_left ((min_le_right _ _).trans this)]; simp

/-- Equality on real continuous compactly supported functions extends to all bounded Borel
functions. -/
lemma GoodL.ext_Cc {L M : (ℝ → ℂ) → ℂ} (hL : GoodL L) (hM : GoodL M)
    (h : ∀ g : ℝ → ℝ, Continuous g → HasCompactSupport g →
      L (fun x => (g x : ℂ)) = M (fun x => (g x : ℂ))) :
    ∀ f, IsBoundedBorel f → L f = M f := by
  have hIoo := hL.eq_Ioo hM h
  have hone : L 1 = M 1 := by
    refine hL.eq_of_lim hM (fun n => (Set.Ioo (-(n : ℝ)) n).indicator 1) 1 1
      (fun n => isBoundedBorel_indicator measurableSet_Ioo) (isBoundedBorel_const 1) ?_ ?_
      (fun n => hIoo _ _)
    · intro n x
      by_cases hx : x ∈ Set.Ioo (-(n : ℝ)) n
      · (try simp only); rw [Set.indicator_of_mem hx]; simp
      · (try simp only); rw [Set.indicator_of_notMem hx]; simp
    · intro x
      obtain ⟨N, hN⟩ := exists_nat_gt |x|
      refine tendsto_const_nhds.congr' (eventually_atTop.2 ⟨N, fun n hn => ?_⟩)
      have : x ∈ Set.Ioo (-(n : ℝ)) n := by
        have : (N : ℝ) ≤ n := by exact_mod_cast hn
        constructor <;> linarith [abs_lt.1 (hN.trans_le this)]
      simp only; rw [Set.indicator_of_mem this]
  apply hL.ext_ind hM
  intro Ω hΩ
  have hgen : (inferInstance : MeasurableSpace ℝ) =
      MeasurableSpace.generateFrom (⋃ (a : ℚ) (b : ℚ) (_ : a < b), {Set.Ioo (a : ℝ) (b : ℝ)}) :=
    Real.borel_eq_generateFrom_Ioo_rat
  refine MeasurableSpace.induction_on_inter (C := fun Ω _ => L (Ω.indicator 1) = M (Ω.indicator 1))
    hgen Real.isPiSystem_Ioo_rat ?_ ?_ ?_ ?_ Ω hΩ
  · simp only [Set.indicator_empty]
    exact hL.zero.trans hM.zero.symm
  · intro t ht
    simp only [Set.mem_iUnion, Set.mem_singleton_iff] at ht
    obtain ⟨a, b, -, rfl⟩ := ht
    exact hIoo a b
  · intro t htm ht
    have e : tᶜ.indicator (1 : ℝ → ℂ) = 1 + (-1 : ℂ) • t.indicator 1 := by
      rw [Set.indicator_compl]; simp [sub_eq_add_neg]
    rw [e, hL.add 1 _ (isBoundedBorel_const 1) (ibb_smul _ (isBoundedBorel_indicator htm)),
      hM.add 1 _ (isBoundedBorel_const 1) (ibb_smul _ (isBoundedBorel_indicator htm)),
      hL.smul _ _ (isBoundedBorel_indicator htm), hM.smul _ _ (isBoundedBorel_indicator htm),
      ht, hone]
  · intro F hdisj hFm hF
    let As : ℕ → Set ℝ := fun N => ⋃ i ∈ Finset.range N, F i
    have hmono : Monotone As := by
      intro m n hmn
      exact Set.biUnion_subset_biUnion_left (fun i hi => by
        have := Finset.mem_range.1 hi; exact Finset.mem_range.2 (by omega))
    have hU : (⋃ N, As N) = ⋃ i, F i := by
      ext x
      simp only [As, Set.mem_iUnion, Finset.mem_range]
      constructor
      · rintro ⟨N, i, -, hi⟩; exact ⟨i, hi⟩
      · rintro ⟨i, hi⟩; exact ⟨i + 1, i, by omega, hi⟩
    have hsum : ∀ N, (As N).indicator (1 : ℝ → ℂ) = ∑ i ∈ Finset.range N, (F i).indicator 1 := by
      intro N
      funext x
      rw [Finset.sum_apply]
      exact Finset.indicator_biUnion_apply _ _
        (fun i _ j _ hij => hdisj hij) x
    refine hL.eq_of_lim hM (fun N => (As N).indicator 1) _ 1 ?_
      (isBoundedBorel_indicator (MeasurableSet.iUnion hFm)) ?_ ?_ ?_
    · intro N
      exact isBoundedBorel_indicator (MeasurableSet.biUnion (Finset.range N).countable_toSet
        (fun i _ => hFm i))
    · intro N x
      by_cases hx : x ∈ As N
      · (try simp only); rw [Set.indicator_of_mem hx]; simp
      · (try simp only); rw [Set.indicator_of_notMem hx]; simp
    · intro x
      rw [← hU]
      exact (hmono.tendsto_indicator _ 1 x).mono_right (pure_le_nhds _)
    · intro N
      try simp only
      rw [hsum, hL.finset_sum _ _ (fun i => isBoundedBorel_indicator (hFm i)),
        hM.finset_sum _ _ (fun i => isBoundedBorel_indicator (hFm i))]
      exact Finset.sum_congr rfl (fun i _ => hF i)

end TeschlQM.Spectral.BFC


open MeasureTheory Filter Topology CompactlySupported
open scoped ENNReal InnerProductSpace ComplexConjugate

namespace TeschlQM.Spectral.Constr

open TeschlQM.Spectral TeschlQM.Spectral.Circ TeschlQM.Spectral.BFC

/-- Trapezoidal cut-off, `1` on `[-n, n]` and `0` outside `[-n-1, n+1]`. -/
noncomputable def trap (n : ℝ) (x : ℝ) : ℝ := max 0 (min 1 (n + 1 - |x|))

lemma trap_continuous (n : ℝ) : Continuous (trap n) := by unfold trap; fun_prop

lemma trap_nonneg (n x : ℝ) : 0 ≤ trap n x := le_max_left _ _

lemma trap_le_one (n x : ℝ) : trap n x ≤ 1 := max_le zero_le_one (min_le_left _ _)

lemma trap_eq_one {n x : ℝ} (h : |x| ≤ n) : trap n x = 1 := by
  unfold trap
  rw [min_eq_left (by linarith), max_eq_right zero_le_one]

lemma trap_hasCompactSupport (n : ℝ) : HasCompactSupport (trap n) := by
  refine HasCompactSupport.intro (isCompact_Icc (a := -(n + 1)) (b := n + 1)) (fun x hx => ?_)
  have : n + 1 < |x| := by
    simp only [Set.mem_Icc, not_and_or, not_le] at hx
    rcases hx with hx | hx
    · linarith [neg_abs_le x]
    · linarith [le_abs_self x]
  unfold trap
  rw [max_eq_left ((min_le_right _ _).trans (by linarith))]

lemma tendsto_trap (x : ℝ) : Tendsto (fun n : ℕ => trap n x) atTop (𝓝 1) := by
  obtain ⟨N, hN⟩ := exists_nat_ge |x|
  refine tendsto_const_nhds.congr' (eventually_atTop.2 ⟨N, fun n hn => ?_⟩)
  have : (N : ℝ) ≤ n := by exact_mod_cast hn
  exact (trap_eq_one (by linarith)).symm

lemma isCc_trap (n : ℝ) : IsCc (fun x => (trap n x : ℂ)) :=
  IsCc.ofReal (trap_continuous n) (trap_hasCompactSupport n)

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {U : H →L[ℂ] H}

lemma inner_self_im_of_sa {T : H →L[ℂ] H} (hT : star T = T) (ψ : H) :
    (⟪ψ, T ψ⟫_ℂ).im = 0 := by
  have h : ⟪ψ, T ψ⟫_ℂ = ⟪T ψ, ψ⟫_ℂ := by
    conv_rhs => rw [← hT]
    rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_left]
  have h2 := inner_conj_symm (𝕜 := ℂ) (T ψ) ψ
  rw [← h] at h2
  have := congrArg Complex.im h2
  rw [Complex.conj_im] at this
  linarith

lemma isCc_cc (g : C_c(ℝ, ℝ)) : IsCc (fun x => (g x : ℂ)) :=
  IsCc.ofReal g.continuous g.hasCompactSupport

lemma FC_inner_nonneg' (hU : U ∈ unitary (H →L[ℂ] H)) (g : C_c(ℝ, ℝ)) (hg : ∀ x, 0 ≤ g x)
    (ψ : H) : ∃ r : ℝ, 0 ≤ r ∧ ⟪ψ, FC U (fun x => (g x : ℂ)) ψ⟫_ℂ = r :=
  FC_inner_nonneg hU g.continuous g.hasCompactSupport hg ψ

/-- The positive functional `g ↦ ⟨ψ, g(U) ψ⟩` on `C_c(ℝ, ℝ)`. -/
noncomputable def LamL (hU : U ∈ unitary (H →L[ℂ] H)) (ψ : H) : C_c(ℝ, ℝ) →ₗ[ℝ] ℝ where
  toFun g := (⟪ψ, FC U (fun x => (g x : ℂ)) ψ⟫_ℂ).re
  map_add' g₁ g₂ := by
    have : (fun x => (((g₁ + g₂) x : ℝ) : ℂ)) =
        (fun x => (g₁ x : ℂ)) + (fun x => (g₂ x : ℂ)) := by
      funext x; simp
    rw [this, FC_add hU (isCc_cc g₁) (isCc_cc g₂)]
    simp
  map_smul' c g := by
    have : (fun x => (((c • g) x : ℝ) : ℂ)) = (c : ℂ) • (fun x => (g x : ℂ)) := by
      funext x; simp
    rw [this, FC_smul hU _ (isCc_cc g)]
    simp

noncomputable def Lam (hU : U ∈ unitary (H →L[ℂ] H)) (ψ : H) : C_c(ℝ, ℝ) →ₚ[ℝ] ℝ :=
  PositiveLinearMap.mk₀ (LamL hU ψ) (fun g hg => by
    obtain ⟨r, hr, he⟩ := FC_inner_nonneg' hU g (fun x => hg x) ψ
    change 0 ≤ (⟪ψ, FC U (fun x => (g x : ℂ)) ψ⟫_ℂ).re
    rw [he]; simpa using hr)

/-- The spectral measure of `ψ` with respect to the unitary `U`, transported to `ℝ`. -/
noncomputable def mu (hU : U ∈ unitary (H →L[ℂ] H)) (ψ : H) : Measure ℝ :=
  RealRMK.rieszMeasure (Lam hU ψ)

lemma integral_mu (hU : U ∈ unitary (H →L[ℂ] H)) (ψ : H) {g : ℝ → ℝ} (hg : Continuous g)
    (hs : HasCompactSupport g) :
    ∫ x, (g x : ℂ) ∂mu hU ψ = ⟪ψ, FC U (fun x => (g x : ℂ)) ψ⟫_ℂ := by
  let G : C_c(ℝ, ℝ) := ⟨⟨g, hg⟩, hs⟩
  have h1 : ∫ x, g x ∂mu hU ψ = (⟪ψ, FC U (fun x => (g x : ℂ)) ψ⟫_ℂ).re :=
    RealRMK.integral_rieszMeasure (Lam hU ψ) G
  have h2 := inner_self_im_of_sa (FC_real_selfAdjoint (U := U) (g := g)) ψ
  rw [integral_complex_ofReal, h1]
  apply Complex.ext <;> simp [h2]

lemma mu_univ_le (hU : U ∈ unitary (H →L[ℂ] H)) (ψ : H) :
    mu hU ψ Set.univ ≤ ENNReal.ofReal (‖ψ‖ ^ 2) := by
  have hUn : (⋃ n : ℕ, Set.Icc (-(n : ℝ)) n) = Set.univ := by
    ext x
    simp only [Set.mem_iUnion, Set.mem_Icc, Set.mem_univ, iff_true]
    obtain ⟨n, hn⟩ := exists_nat_ge |x|
    exact ⟨n, by linarith [neg_abs_le x], by linarith [le_abs_self x]⟩
  have hmono : Monotone (fun n : ℕ => Set.Icc (-(n : ℝ)) n) := by
    intro m n hmn
    have : (m : ℝ) ≤ n := by exact_mod_cast hmn
    exact Set.Icc_subset_Icc (by linarith) this
  rw [← hUn, hmono.measure_iUnion]
  refine iSup_le (fun n => ?_)
  let TR : C_c(ℝ, ℝ) := ⟨⟨trap n, trap_continuous n⟩, trap_hasCompactSupport n⟩
  have h := RealRMK.rieszMeasure_le_of_eq_one (Lam hU ψ) (f := TR) (fun x => trap_nonneg n x)
    isCompact_Icc (fun x hx => trap_eq_one (abs_le.2 hx))
  refine h.trans (ENNReal.ofReal_le_ofReal ?_)
  change (⟪ψ, FC U (fun x => (trap n x : ℂ)) ψ⟫_ℂ).re ≤ ‖ψ‖ ^ 2
  have hn : ‖FC U (fun x => (trap n x : ℂ))‖ ≤ 1 :=
    FC_norm_le zero_le_one (fun x => by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (trap_nonneg n x)]
      exact trap_le_one n x)
  calc (⟪ψ, FC U (fun x => (trap n x : ℂ)) ψ⟫_ℂ).re ≤ ‖⟪ψ, FC U (fun x => (trap n x : ℂ)) ψ⟫_ℂ‖ :=
        Complex.re_le_norm _
    _ ≤ ‖ψ‖ * ‖FC U (fun x => (trap n x : ℂ)) ψ‖ := norm_inner_le_norm _ _
    _ ≤ ‖ψ‖ * (1 * ‖ψ‖) := by
        gcongr
        exact (ContinuousLinearMap.le_opNorm _ _).trans (by gcongr)
    _ = ‖ψ‖ ^ 2 := by ring

lemma mu_finite (hU : U ∈ unitary (H →L[ℂ] H)) (ψ : H) : IsFiniteMeasure (mu hU ψ) :=
  ⟨(mu_univ_le hU ψ).trans_lt ENNReal.ofReal_lt_top⟩

end TeschlQM.Spectral.Constr


open MeasureTheory Filter Topology
open scoped ENNReal InnerProductSpace ComplexConjugate

namespace TeschlQM.Spectral.Constr

open TeschlQM.Spectral TeschlQM.Spectral.Circ TeschlQM.Spectral.BFC

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {U : H →L[ℂ] H}

/-- The polarized form `∫ h dμ_{φ,ψ}`. -/
noncomputable def B (hU : U ∈ unitary (H →L[ℂ] H)) (h : ℝ → ℂ) (φ ψ : H) : ℂ :=
  (1 / 4 : ℂ) * ((∫ x, h x ∂mu hU (φ + ψ)) - (∫ x, h x ∂mu hU (φ - ψ))
    + Complex.I * (∫ x, h x ∂mu hU (φ - Complex.I • ψ))
    - Complex.I * (∫ x, h x ∂mu hU (φ + Complex.I • ψ)))

lemma goodL_mu (hU : U ∈ unitary (H →L[ℂ] H)) (v : H) :
    GoodL (fun h => ∫ x, h x ∂mu hU v) :=
  @goodL_integral (mu hU v) (mu_finite hU v)

lemma goodL_B (hU : U ∈ unitary (H →L[ℂ] H)) (φ ψ : H) : GoodL (fun h => B hU h φ ψ) :=
  ((((goodL_mu hU _).sub' (goodL_mu hU _)).add' ((goodL_mu hU _).const_mul Complex.I)).sub'
    ((goodL_mu hU _).const_mul Complex.I)).const_mul (1 / 4)

lemma B_Cc (hU : U ∈ unitary (H →L[ℂ] H)) {g : ℝ → ℝ} (hg : Continuous g)
    (hs : HasCompactSupport g) (φ ψ : H) :
    B hU (fun x => (g x : ℂ)) φ ψ = ⟪φ, FC U (fun x => (g x : ℂ)) ψ⟫_ℂ := by
  rw [polarization (FC U (fun x => (g x : ℂ))) φ ψ]
  unfold B
  rw [integral_mu hU _ hg hs, integral_mu hU _ hg hs, integral_mu hU _ hg hs,
    integral_mu hU _ hg hs]

lemma B_add_right (hU : U ∈ unitary (H →L[ℂ] H)) {h : ℝ → ℂ} (hh : IsBoundedBorel h)
    (φ ψ₁ ψ₂ : H) : B hU h φ (ψ₁ + ψ₂) = B hU h φ ψ₁ + B hU h φ ψ₂ :=
  (goodL_B hU φ (ψ₁ + ψ₂)).ext_Cc ((goodL_B hU φ ψ₁).add' (goodL_B hU φ ψ₂))
    (fun g hg hs => by simp only [B_Cc hU hg hs, map_add, inner_add_right]) h hh

lemma B_smul_right (hU : U ∈ unitary (H →L[ℂ] H)) {h : ℝ → ℂ} (hh : IsBoundedBorel h)
    (c : ℂ) (φ ψ : H) : B hU h φ (c • ψ) = c * B hU h φ ψ :=
  (goodL_B hU φ (c • ψ)).ext_Cc ((goodL_B hU φ ψ).const_mul c)
    (fun g hg hs => by simp only [B_Cc hU hg hs, map_smul, inner_smul_right]) h hh

lemma B_add_left (hU : U ∈ unitary (H →L[ℂ] H)) {h : ℝ → ℂ} (hh : IsBoundedBorel h)
    (φ₁ φ₂ ψ : H) : B hU h (φ₁ + φ₂) ψ = B hU h φ₁ ψ + B hU h φ₂ ψ :=
  (goodL_B hU (φ₁ + φ₂) ψ).ext_Cc ((goodL_B hU φ₁ ψ).add' (goodL_B hU φ₂ ψ))
    (fun g hg hs => by simp only [B_Cc hU hg hs, inner_add_left]) h hh

lemma B_smul_left (hU : U ∈ unitary (H →L[ℂ] H)) {h : ℝ → ℂ} (hh : IsBoundedBorel h)
    (c : ℂ) (φ ψ : H) : B hU h (c • φ) ψ = conj c * B hU h φ ψ :=
  (goodL_B hU (c • φ) ψ).ext_Cc ((goodL_B hU φ ψ).const_mul (conj c))
    (fun g hg hs => by simp only [B_Cc hU hg hs, inner_smul_left]) h hh

lemma norm_integral_mu_le (hU : U ∈ unitary (H →L[ℂ] H)) {h : ℝ → ℂ} {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ x, ‖h x‖ ≤ C) (v : H) : ‖∫ x, h x ∂mu hU v‖ ≤ C * ‖v‖ ^ 2 := by
  haveI := mu_finite hU v
  refine (norm_integral_le_of_norm_le_const (Eventually.of_forall hb)).trans ?_
  gcongr
  exact ENNReal.toReal_le_of_le_ofReal (sq_nonneg _) (mu_univ_le hU v)

lemma B_bound (hU : U ∈ unitary (H →L[ℂ] H)) {h : ℝ → ℂ} {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ x, ‖h x‖ ≤ C) (φ ψ : H) : ‖B hU h φ ψ‖ ≤ C * (‖φ‖ ^ 2 + ‖ψ‖ ^ 2) := by
  have p1 := parallelogram_law_with_norm ℂ φ ψ
  have p2 := parallelogram_law_with_norm ℂ φ (Complex.I • ψ)
  have hI : ‖Complex.I • ψ‖ = ‖ψ‖ := by rw [norm_smul, Complex.norm_I, one_mul]
  rw [hI] at p2
  have e1 := norm_integral_mu_le hU hC hb (φ + ψ)
  have e2 := norm_integral_mu_le hU hC hb (φ - ψ)
  have e3 := norm_integral_mu_le hU hC hb (φ - Complex.I • ψ)
  have e4 := norm_integral_mu_le hU hC hb (φ + Complex.I • ψ)
  unfold B
  rw [norm_mul]
  have : ‖(1 / 4 : ℂ)‖ = 1 / 4 := by norm_num
  rw [this]
  have t : ‖(∫ x, h x ∂mu hU (φ + ψ)) - (∫ x, h x ∂mu hU (φ - ψ))
    + Complex.I * (∫ x, h x ∂mu hU (φ - Complex.I • ψ))
    - Complex.I * (∫ x, h x ∂mu hU (φ + Complex.I • ψ))‖ ≤
      C * ‖φ + ψ‖ ^ 2 + C * ‖φ - ψ‖ ^ 2 + C * ‖φ - Complex.I • ψ‖ ^ 2
        + C * ‖φ + Complex.I • ψ‖ ^ 2 := by
    refine (norm_sub_le _ _).trans ?_
    refine (add_le_add (norm_add_le _ _) le_rfl).trans ?_
    refine (add_le_add (add_le_add (norm_sub_le _ _) le_rfl) le_rfl).trans ?_
    rw [norm_mul, norm_mul, Complex.norm_I, one_mul, one_mul]
    linarith
  nlinarith

lemma B_bound2 (hU : U ∈ unitary (H →L[ℂ] H)) {h : ℝ → ℂ} (hh : IsBoundedBorel h) {C : ℝ}
    (hC : 0 ≤ C) (hb : ∀ x, ‖h x‖ ≤ C) (φ ψ : H) : ‖B hU h φ ψ‖ ≤ 2 * C * ‖φ‖ * ‖ψ‖ := by
  by_cases hφ : φ = 0
  · have : B hU h φ ψ = 0 := by
      rw [hφ, show (0 : H) = (0 : ℂ) • (0 : H) by simp, B_smul_left hU hh]; simp
    rw [this, norm_zero]; positivity
  by_cases hψ : ψ = 0
  · have : B hU h φ ψ = 0 := by
      rw [hψ, show (0 : H) = (0 : ℂ) • (0 : H) by simp, B_smul_right hU hh]; simp
    rw [this, norm_zero]; positivity
  have ha : 0 < ‖φ‖ := norm_pos_iff.2 hφ
  have hb' : 0 < ‖ψ‖ := norm_pos_iff.2 hψ
  set t : ℝ := Real.sqrt (‖ψ‖ / ‖φ‖) with htdef
  have ht : 0 < t := Real.sqrt_pos.2 (by positivity)
  have ht2 : t ^ 2 = ‖ψ‖ / ‖φ‖ := Real.sq_sqrt (by positivity)
  have e : B hU h φ ψ = B hU h ((t : ℂ) • φ) (((t⁻¹ : ℝ) : ℂ) • ψ) := by
    rw [B_smul_left hU hh, B_smul_right hU hh, Complex.conj_ofReal, ← mul_assoc,
      ← Complex.ofReal_mul, mul_inv_cancel₀ ht.ne', Complex.ofReal_one, one_mul]
  have hB := B_bound hU hC hb ((t : ℂ) • φ) (((t⁻¹ : ℝ) : ℂ) • ψ)
  rw [← e, norm_smul, norm_smul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
    Real.norm_eq_abs, abs_of_pos ht, abs_of_pos (inv_pos.2 ht)] at hB
  have h1 : (t * ‖φ‖) ^ 2 = ‖φ‖ * ‖ψ‖ := by
    rw [mul_pow, ht2]; field_simp
  have h2 : (t⁻¹ * ‖ψ‖) ^ 2 = ‖φ‖ * ‖ψ‖ := by
    rw [mul_pow, inv_pow, ht2]; field_simp
  rw [h1, h2] at hB
  linarith

end TeschlQM.Spectral.Constr


open MeasureTheory Filter Topology
open scoped ENNReal InnerProductSpace ComplexConjugate

namespace TeschlQM.Spectral.Constr

open TeschlQM.Spectral TeschlQM.Spectral.Circ TeschlQM.Spectral.BFC

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {U : H →L[ℂ] H}

lemma ibb_bound {h : ℝ → ℂ} (hh : IsBoundedBorel h) : ∃ C, 0 ≤ C ∧ ∀ x, ‖h x‖ ≤ C :=
  let ⟨C, hC⟩ := hh.2
  ⟨C, (norm_nonneg _).trans (hC 0), hC⟩

/-- The bounded sesquilinear form `(φ, ψ) ↦ ∫ h dμ_{φ,ψ}`. -/
noncomputable def formCLM (hU : U ∈ unitary (H →L[ℂ] H)) {h : ℝ → ℂ} (hh : IsBoundedBorel h) :
    H →L⋆[ℂ] H →L[ℂ] ℂ :=
  LinearMap.mkContinuous₂
    (LinearMap.mk₂'ₛₗ (starRingEnd ℂ) (RingHom.id ℂ) (fun φ ψ => B hU h φ ψ)
      (fun φ₁ φ₂ ψ => B_add_left hU hh φ₁ φ₂ ψ) (fun c φ ψ => B_smul_left hU hh c φ ψ)
      (fun φ ψ₁ ψ₂ => B_add_right hU hh φ ψ₁ ψ₂) (fun c φ ψ => B_smul_right hU hh c φ ψ))
    (2 * (ibb_bound hh).choose)
    (fun φ ψ => B_bound2 hU hh (ibb_bound hh).choose_spec.1 (ibb_bound hh).choose_spec.2 φ ψ)

open Classical in
/-- The Borel functional calculus `h ↦ h(U)` (transported to `ℝ`). -/
noncomputable def Phi (hU : U ∈ unitary (H →L[ℂ] H)) (h : ℝ → ℂ) : H →L[ℂ] H :=
  if hh : IsBoundedBorel h then
    ContinuousLinearMap.adjoint (InnerProductSpace.continuousLinearMapOfBilin (formCLM hU hh))
  else 0

lemma Phi_inner (hU : U ∈ unitary (H →L[ℂ] H)) {h : ℝ → ℂ} (hh : IsBoundedBorel h) (φ ψ : H) :
    ⟪φ, Phi hU h ψ⟫_ℂ = B hU h φ ψ := by
  rw [Phi, dif_pos hh, ContinuousLinearMap.adjoint_inner_right,
    InnerProductSpace.continuousLinearMapOfBilin_apply]
  rfl

omit [CompleteSpace H] in
lemma op_ext {T S : H →L[ℂ] H} (h : ∀ φ ψ, ⟪φ, T ψ⟫_ℂ = ⟪φ, S ψ⟫_ℂ) : T = S := by
  ext ψ
  exact ext_inner_left ℂ (fun φ => h φ ψ)

lemma Phi_Cc (hU : U ∈ unitary (H →L[ℂ] H)) {g : ℝ → ℝ} (hg : Continuous g)
    (hs : HasCompactSupport g) : Phi hU (fun x => (g x : ℂ)) = FC U (fun x => (g x : ℂ)) := by
  refine op_ext (fun φ ψ => ?_)
  have hb : IsBoundedBorel (fun x => (g x : ℂ)) := by
    obtain ⟨C, hC⟩ := hg.bounded_above_of_compact_support hs
    exact ⟨(Complex.continuous_ofReal.comp hg).measurable, C, fun x => by
      rw [Complex.norm_real]; exact hC x⟩
  rw [Phi_inner hU hb, B_Cc hU hg hs]

lemma Phi_add (hU : U ∈ unitary (H →L[ℂ] H)) {f g : ℝ → ℂ} (hf : IsBoundedBorel f)
    (hg : IsBoundedBorel g) : Phi hU (f + g) = Phi hU f + Phi hU g := by
  refine op_ext (fun φ ψ => ?_)
  rw [Phi_inner hU (ibb_add hf hg), ContinuousLinearMap.add_apply, inner_add_right,
    Phi_inner hU hf, Phi_inner hU hg]
  exact (goodL_B hU φ ψ).add f g hf hg

lemma Phi_smul (hU : U ∈ unitary (H →L[ℂ] H)) (c : ℂ) {f : ℝ → ℂ} (hf : IsBoundedBorel f) :
    Phi hU (c • f) = c • Phi hU f := by
  refine op_ext (fun φ ψ => ?_)
  rw [Phi_inner hU (ibb_smul c hf), ContinuousLinearMap.smul_apply, inner_smul_right,
    Phi_inner hU hf]
  exact (goodL_B hU φ ψ).smul c f hf

lemma isBoundedBorel_of_isCc {f : ℝ → ℂ} (hf : IsCc f) : IsBoundedBorel f := by
  obtain ⟨C, hC⟩ := hf.1.bounded_above_of_compact_support hf.2
  exact ⟨hf.1.measurable, C, hC⟩

lemma Phi_Cc' (hU : U ∈ unitary (H →L[ℂ] H)) {f : ℝ → ℂ} (hf : IsCc f) :
    Phi hU f = FC U f := by
  have hre : Continuous (fun x => (f x).re) := Complex.continuous_re.comp hf.1
  have him : Continuous (fun x => (f x).im) := Complex.continuous_im.comp hf.1
  have hres : HasCompactSupport (fun x => (f x).re) := hf.2.comp_left Complex.zero_re
  have hims : HasCompactSupport (fun x => (f x).im) := hf.2.comp_left Complex.zero_im
  have e : f = (fun x => ((f x).re : ℂ)) + Complex.I • (fun x => ((f x).im : ℂ)) := by
    funext x
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [mul_comm]; exact (Complex.re_add_im _).symm
  rw [e, Phi_add hU (isBoundedBorel_of_isCc (IsCc.ofReal hre hres))
      (ibb_smul _ (isBoundedBorel_of_isCc (IsCc.ofReal him hims))),
    Phi_smul hU _ (isBoundedBorel_of_isCc (IsCc.ofReal him hims)), Phi_Cc hU hre hres,
    Phi_Cc hU him hims, FC_add hU (IsCc.ofReal hre hres) ((IsCc.ofReal him hims).smul _),
    FC_smul hU _ (IsCc.ofReal him hims)]

lemma B_conj (hU : U ∈ unitary (H →L[ℂ] H)) {h : ℝ → ℂ} (hh : IsBoundedBorel h) (φ ψ : H) :
    B hU h φ ψ = conj (B hU (star h) ψ φ) := by
  refine (goodL_B hU φ ψ).ext_Cc (goodL_B hU ψ φ).conj (fun g hg hs => ?_) h hh
  have hs' : star (fun x => (g x : ℂ)) = (fun x => (g x : ℂ)) := by funext x; simp
  rw [hs', B_Cc hU hg hs, B_Cc hU hg hs, inner_conj_symm]
  conv_rhs => rw [← FC_real_selfAdjoint (U := U) (g := g)]
  rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_left]

lemma Phi_star (hU : U ∈ unitary (H →L[ℂ] H)) {h : ℝ → ℂ} (hh : IsBoundedBorel h) :
    star (Phi hU h) = Phi hU (star h) := by
  refine op_ext (fun φ ψ => ?_)
  rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_right,
    ← inner_conj_symm, Phi_inner hU hh, Phi_inner hU (ibb_star hh), B_conj hU (ibb_star hh),
    star_star]

lemma Phi_mul_Cc (hU : U ∈ unitary (H →L[ℂ] H)) {g : ℝ → ℝ} (hg : Continuous g)
    (hs : HasCompactSupport g) {h : ℝ → ℂ} (hh : IsBoundedBorel h) :
    Phi hU ((fun x => (g x : ℂ)) * h) = FC U (fun x => (g x : ℂ)) * Phi hU h := by
  have hgb : IsBoundedBorel (fun x => (g x : ℂ)) := isBoundedBorel_of_isCc (IsCc.ofReal hg hs)
  refine op_ext (fun φ ψ => ?_)
  rw [Phi_inner hU (ibb_mul hgb hh), ContinuousLinearMap.mul_apply]
  conv_rhs => rw [← FC_real_selfAdjoint (U := U) (g := g)]
  rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_right,
    Phi_inner hU hh]
  refine ((goodL_B hU φ ψ).comp_mul hgb).ext_Cc (goodL_B hU _ ψ) (fun k hk hks => ?_) h hh
  have e : (fun x => (g x : ℂ)) * (fun x => (k x : ℂ)) = fun x => ((g x * k x : ℝ) : ℂ) := by
    funext x; simp
  rw [e, B_Cc hU (g := fun x => g x * k x) (hg.mul hk) (hs.mul_right), B_Cc hU hk hks, ← e,
    FC_mul hU (IsCc.ofReal hg hs) (IsCc.ofReal hk hks), ContinuousLinearMap.mul_apply]
  conv_lhs => rw [← FC_real_selfAdjoint (U := U) (g := g)]
  rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_right]

lemma Phi_mul (hU : U ∈ unitary (H →L[ℂ] H)) {f h : ℝ → ℂ} (hf : IsBoundedBorel f)
    (hh : IsBoundedBorel h) : Phi hU (f * h) = Phi hU f * Phi hU h := by
  refine op_ext (fun φ ψ => ?_)
  rw [Phi_inner hU (ibb_mul hf hh), ContinuousLinearMap.mul_apply, Phi_inner hU hf]
  have hL : GoodL (fun f => B hU (f * h) φ ψ) := by
    have := (goodL_B hU φ ψ).comp_mul hh
    simpa only [mul_comm h] using this
  refine hL.ext_Cc (goodL_B hU φ _) (fun g hg hs => ?_) f hf
  rw [← Phi_inner hU (ibb_mul (isBoundedBorel_of_isCc (IsCc.ofReal hg hs)) hh),
    Phi_mul_Cc hU hg hs hh, B_Cc hU hg hs, ContinuousLinearMap.mul_apply]

end TeschlQM.Spectral.Constr


open MeasureTheory Filter Topology
open scoped ENNReal InnerProductSpace ComplexConjugate

namespace TeschlQM.Spectral.Constr

open TeschlQM.Shared TeschlQM.Spectral TeschlQM.Spectral.Circ TeschlQM.Spectral.BFC

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {U : H →L[ℂ] H}

lemma Phi_sub (hU : U ∈ unitary (H →L[ℂ] H)) {f g : ℝ → ℂ} (hf : IsBoundedBorel f)
    (hg : IsBoundedBorel g) : Phi hU (f - g) = Phi hU f - Phi hU g := by
  have e : f - g = f + (-1 : ℂ) • g := by funext x; simp [sub_eq_add_neg]
  rw [e, Phi_add hU hf (ibb_smul _ hg), Phi_smul hU _ hg]
  simp [sub_eq_add_neg]

lemma norm_Phi_sq (hU : U ∈ unitary (H →L[ℂ] H)) {k : ℝ → ℂ} (hk : IsBoundedBorel k) (ψ : H) :
    ((‖Phi hU k ψ‖ ^ 2 : ℝ) : ℂ) = B hU (star k * k) ψ ψ := by
  rw [← Phi_inner hU (ibb_mul (ibb_star hk) hk), Phi_mul hU (ibb_star hk) hk, ← Phi_star hU hk,
    ContinuousLinearMap.mul_apply, ContinuousLinearMap.star_eq_adjoint,
    ContinuousLinearMap.adjoint_inner_right, inner_self_eq_norm_sq_to_K]
  simp

lemma Phi_tendsto (hU : U ∈ unitary (H →L[ℂ] H)) {fs : ℕ → ℝ → ℂ} {f : ℝ → ℂ}
    (hfs : ∀ n, IsBoundedBorel (fs n)) (hf : IsBoundedBorel f) {C : ℝ}
    (hb : ∀ n x, ‖fs n x‖ ≤ C) (hl : ∀ x, Tendsto (fun n => fs n x) atTop (𝓝 (f x))) (ψ : H) :
    Tendsto (fun n => Phi hU (fs n) ψ) atTop (𝓝 (Phi hU f ψ)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  obtain ⟨D, hD0, hD⟩ := ibb_bound hf
  have hk : ∀ n, IsBoundedBorel (fs n - f) := fun n => ibb_sub (hfs n) hf
  have key : ∀ n, ((‖Phi hU (fs n) ψ - Phi hU f ψ‖ ^ 2 : ℝ) : ℂ) =
      B hU (star (fs n - f) * (fs n - f)) ψ ψ := by
    intro n
    rw [← ContinuousLinearMap.sub_apply, ← Phi_sub hU (hfs n) hf, norm_Phi_sq hU (hk n)]
  have hB : Tendsto (fun n => B hU (star (fs n - f) * (fs n - f)) ψ ψ) atTop (𝓝 0) := by
    have := (goodL_B hU ψ ψ).lim (fun n => star (fs n - f) * (fs n - f)) 0 ((C + D) ^ 2)
      (fun n => ibb_mul (ibb_star (hk n)) (hk n)) (isBoundedBorel_const 0) ?_ ?_
    · rwa [(goodL_B hU ψ ψ).zero] at this
    · intro n x
      simp only [Pi.mul_apply, Pi.star_apply, Pi.sub_apply, norm_mul, norm_star]
      have : ‖fs n x - f x‖ ≤ C + D := (norm_sub_le _ _).trans (add_le_add (hb n x) (hD x))
      nlinarith [norm_nonneg (fs n x - f x)]
    · intro x
      have h1 : Tendsto (fun n => fs n x - f x) atTop (𝓝 0) := by
        simpa using (hl x).sub_const (f x)
      have h2 := (h1.star).mul h1
      simpa using h2
  have hre : Tendsto (fun n => ‖Phi hU (fs n) ψ - Phi hU f ψ‖ ^ 2) atTop (𝓝 0) := by
    have := (Complex.continuous_re.tendsto 0).comp hB
    simp only [Function.comp_def, ← key, Complex.ofReal_re, Complex.zero_re] at this
    exact this
  have := (Real.continuous_sqrt.tendsto 0).comp hre
  simp only [Function.comp_def, Real.sqrt_sq (norm_nonneg _), Real.sqrt_zero] at this
  exact this

lemma tendsto_trap' (x : ℝ) : Tendsto (fun k : ℕ => trap ((k : ℝ) + 1) x) atTop (𝓝 1) := by
  obtain ⟨N, hN⟩ := exists_nat_ge |x|
  refine tendsto_const_nhds.congr' (eventually_atTop.2 ⟨N, fun n hn => ?_⟩)
  have : (N : ℝ) ≤ n := by exact_mod_cast hn
  exact (trap_eq_one (by linarith)).symm

lemma ibb_trap (n : ℝ) : IsBoundedBorel (fun x => (trap n x : ℂ)) :=
  isBoundedBorel_of_isCc (isCc_trap n)

lemma norm_trap_le (n x : ℝ) : ‖(trap n x : ℂ)‖ ≤ 1 := by
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (trap_nonneg n x)]
  exact trap_le_one n x

lemma B_trap_tendsto (hU : U ∈ unitary (H →L[ℂ] H)) (φ ψ : H) :
    Tendsto (fun k : ℕ => B hU (fun x => (trap ((k : ℝ) + 1) x : ℂ)) φ ψ) atTop
      (𝓝 (B hU 1 φ ψ)) :=
  (goodL_B hU φ ψ).lim _ 1 1 (fun k => ibb_trap _) (isBoundedBorel_const 1)
    (fun k x => norm_trap_le _ x)
    (fun x => by simpa [Function.comp_def] using (Complex.continuous_ofReal.tendsto 1).comp (tendsto_trap' x))

lemma Phi_one (hU : U ∈ unitary (H →L[ℂ] H)) (hinj : ∀ φ, U φ = φ → φ = 0) :
    Phi hU 1 = 1 := by
  have hnorm : Tendsto (fun k : ℕ => (1 - U) * FC U (fun x => (trap ((k : ℝ) + 1) x : ℂ)))
      atTop (𝓝 (1 - U)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero (fun _ => norm_nonneg _) (fun k => ?_)
      (g := fun k : ℕ => 4 / ((k : ℝ) + 1)) ?_
    · rw [norm_sub_rev]
      exact FC_approx hU (isCc_trap _) (fun x => norm_trap_le _ x) (by positivity)
        (fun x hx => by simp [trap_eq_one hx])
    · have := (tendsto_one_div_add_atTop_nhds_zero_nat).const_mul (4 : ℝ)
      simpa [div_eq_mul_inv] using this
  have key : ∀ φ ψ : H, ⟪φ, (1 - U) (Phi hU 1 ψ)⟫_ℂ = ⟪φ, (1 - U) ψ⟫_ℂ := by
    intro φ ψ
    set w := ContinuousLinearMap.adjoint (1 - U) φ
    have h1 : Tendsto (fun k : ℕ => ⟪φ, ((1 - U) * FC U (fun x => (trap ((k : ℝ) + 1) x : ℂ))) ψ⟫_ℂ)
        atTop (𝓝 ⟪φ, (1 - U) ψ⟫_ℂ) :=
      tendsto_const_nhds.inner (((ContinuousLinearMap.apply ℂ H ψ).continuous.tendsto _).comp hnorm)
    have h2 : ∀ k : ℕ, ⟪φ, ((1 - U) * FC U (fun x => (trap ((k : ℝ) + 1) x : ℂ))) ψ⟫_ℂ =
        B hU (fun x => (trap ((k : ℝ) + 1) x : ℂ)) w ψ := by
      intro k
      rw [ContinuousLinearMap.mul_apply, ← ContinuousLinearMap.adjoint_inner_left,
        ← Phi_Cc hU (trap_continuous _) (trap_hasCompactSupport _), Phi_inner hU (ibb_trap _)]
    simp only [h2] at h1
    rw [← ContinuousLinearMap.adjoint_inner_left, Phi_inner hU (h := 1) (isBoundedBorel_const 1)]
    exact tendsto_nhds_unique (B_trap_tendsto hU w ψ) h1
  have key2 : ∀ ψ, (1 - U) (Phi hU 1 ψ) = (1 - U) ψ := fun ψ =>
    ext_inner_left ℂ (fun φ => key φ ψ)
  ext ψ
  have := key2 ψ
  rw [← sub_eq_zero, ← map_sub] at this
  have h3 : U (Phi hU 1 ψ - ψ) = Phi hU 1 ψ - ψ := by
    have := this
    simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply] at this
    rw [sub_eq_zero] at this
    exact this.symm
  have := hinj _ h3
  rw [sub_eq_zero] at this
  simpa using this

end TeschlQM.Spectral.Constr


open MeasureTheory Filter Topology
open scoped ENNReal InnerProductSpace ComplexConjugate

namespace TeschlQM.Spectral.Constr

open TeschlQM.Shared TeschlQM.Spectral TeschlQM.Spectral.Circ TeschlQM.Spectral.BFC

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {U : H →L[ℂ] H}

lemma kap_continuous : Continuous kap := by
  unfold kap
  exact Continuous.div (by fun_prop) (by fun_prop) add_I_ne_zero

lemma ibb_kap : IsBoundedBorel kap :=
  ⟨kap_continuous.measurable, 1, fun x => (norm_kap x).le⟩

lemma Phi_kap (hU : U ∈ unitary (H →L[ℂ] H)) (hinj : ∀ φ, U φ = φ → φ = 0) :
    Phi hU kap = U := by
  refine op_ext (fun φ ψ => ?_)
  set fk : ℕ → ℝ → ℂ := fun k => kap * (fun x => (trap ((k : ℝ) + 1) x : ℂ))
  have hfk : ∀ k, IsCc (fk k) := fun k => IsCc.mul_left kap_continuous (isCc_trap _)
  have h1 : Tendsto (fun k => B hU (fk k) φ ψ) atTop (𝓝 (B hU kap φ ψ)) := by
    refine (goodL_B hU φ ψ).lim _ _ 1 (fun k => isBoundedBorel_of_isCc (hfk k)) ibb_kap ?_ ?_
    · intro k x
      simp only [fk, Pi.mul_apply, norm_mul, norm_kap, one_mul]
      exact norm_trap_le _ x
    · intro x
      have := ((Complex.continuous_ofReal.tendsto 1).comp (tendsto_trap' x)).const_mul (kap x)
      simpa [fk] using this
  have h2 : ∀ k, B hU (fk k) φ ψ =
      B hU (fun x => (trap ((k : ℝ) + 1) x : ℂ)) (ContinuousLinearMap.adjoint U φ) ψ := by
    intro k
    rw [← Phi_inner hU (isBoundedBorel_of_isCc (hfk k)), Phi_Cc' hU (hfk k),
      FC_kap_mul hU (isCc_trap _), ContinuousLinearMap.mul_apply,
      ← ContinuousLinearMap.adjoint_inner_left,
      ← Phi_Cc hU (trap_continuous _) (trap_hasCompactSupport _), Phi_inner hU (ibb_trap _)]
  simp only [h2] at h1
  have h3 := B_trap_tendsto hU (ContinuousLinearMap.adjoint U φ) ψ
  rw [← Phi_inner hU (h := 1) (isBoundedBorel_const 1), Phi_one hU hinj,
    ContinuousLinearMap.one_apply, ContinuousLinearMap.adjoint_inner_left] at h3
  rw [Phi_inner hU ibb_kap]
  exact tendsto_nhds_unique h1 h3

/-- The projection-valued measure of the unitary `U`, transported to `ℝ`. -/
noncomputable def PU (hU : U ∈ unitary (H →L[ℂ] H)) (Ω : Set ℝ) : H →L[ℂ] H :=
  Phi hU (Ω.indicator 1)

lemma star_indicator_one (Ω : Set ℝ) : star (Ω.indicator (1 : ℝ → ℂ)) = Ω.indicator 1 := by
  funext x; by_cases hx : x ∈ Ω <;> simp [hx]

lemma indicator_one_mul_self (Ω : Set ℝ) :
    Ω.indicator (1 : ℝ → ℂ) * Ω.indicator 1 = Ω.indicator 1 := by
  funext x; by_cases hx : x ∈ Ω <;> simp [hx]

lemma Phi_finset_sum (hU : U ∈ unitary (H →L[ℂ] H)) (s : Finset ℕ) (fs : ℕ → ℝ → ℂ)
    (hfs : ∀ i, IsBoundedBorel (fs i)) :
    Phi hU (∑ i ∈ s, fs i) = ∑ i ∈ s, Phi hU (fs i) := by
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    have := Phi_smul hU 0 (isBoundedBorel_const 0)
    simpa using this
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, Phi_add hU (hfs a)
      (ibb_finset_sum' s fs hfs), ih]

theorem isPVM_PU (hU : U ∈ unitary (H →L[ℂ] H)) (hinj : ∀ φ, U φ = φ → φ = 0) :
    IsProjValuedMeasure (PU hU) := by
  refine ⟨fun Ω hΩ => ⟨?_, ?_⟩, ?_, ?_⟩
  · show star (PU hU Ω) = PU hU Ω
    unfold PU
    rw [Phi_star hU (isBoundedBorel_indicator hΩ), star_indicator_one]
  · show PU hU Ω * PU hU Ω = PU hU Ω
    unfold PU
    rw [← Phi_mul hU (isBoundedBorel_indicator hΩ) (isBoundedBorel_indicator hΩ),
      indicator_one_mul_self]
  · unfold PU
    rw [Set.indicator_univ]
    exact Phi_one hU hinj
  · intro F hFm hdisj ψ
    let As : ℕ → Set ℝ := fun N => ⋃ i ∈ Finset.range N, F i
    have hmono : Monotone As := by
      intro m n hmn
      exact Set.biUnion_subset_biUnion_left (fun i hi => by
        have := Finset.mem_range.1 hi; exact Finset.mem_range.2 (by omega))
    have hU' : (⋃ N, As N) = ⋃ i, F i := by
      ext x
      simp only [As, Set.mem_iUnion, Finset.mem_range]
      constructor
      · rintro ⟨N, i, -, hi⟩; exact ⟨i, hi⟩
      · rintro ⟨i, hi⟩; exact ⟨i + 1, i, by omega, hi⟩
    have hsum : ∀ N, (As N).indicator (1 : ℝ → ℂ) = ∑ i ∈ Finset.range N, (F i).indicator 1 := by
      intro N
      funext x
      rw [Finset.sum_apply]
      exact Finset.indicator_biUnion_apply _ _ (fun i _ j _ hij => hdisj hij) x
    have hAm : ∀ N, MeasurableSet (As N) := fun N =>
      MeasurableSet.biUnion (Finset.range N).countable_toSet (fun i _ => hFm i)
    have heq : ∀ N, ∑ n ∈ Finset.range N, PU hU (F n) ψ = Phi hU ((As N).indicator 1) ψ := by
      intro N
      rw [hsum, Phi_finset_sum hU _ _ (fun i => isBoundedBorel_indicator (hFm i)),
        ContinuousLinearMap.sum_apply]
      rfl
    simp only [heq]
    refine Phi_tendsto hU (fun N => isBoundedBorel_indicator (hAm N))
      (isBoundedBorel_indicator (MeasurableSet.iUnion hFm)) (C := 1) ?_ ?_ ψ
    · intro N x
      by_cases hx : x ∈ As N
      · rw [Set.indicator_of_mem hx]; simp
      · rw [Set.indicator_of_notMem hx]; simp
    · intro x
      rw [← hU']
      exact (hmono.tendsto_indicator _ 1 x).mono_right (pure_le_nhds _)

lemma rep_Phi (hU : U ∈ unitary (H →L[ℂ] H)) (hinj : ∀ φ, U φ = φ → φ = 0) {h : ℝ → ℂ}
    (hh : IsBoundedBorel h) : Rep (PU hU) h (Phi hU h) := by
  have hP := isPVM_PU hU hinj
  intro ψ
  haveI := spectralMeasure_finite hP ψ
  rw [Phi_inner hU hh]
  refine (goodL_B hU ψ ψ).ext_ind (goodL_integral (spectralMeasure (PU hU) ψ))
    (fun Ω hΩ => ?_) h hh
  rw [← Phi_inner hU (isBoundedBorel_indicator hΩ)]
  exact rep_indicator hP hΩ ψ

/-- Spectral theorem for a unitary `U` without eigenvalue `1`, transported to `ℝ` by the
Cayley map: there is a projection-valued measure `P` on `ℝ` with
`U = ∫ (λ - i)/(λ + i) dP(λ)`. -/
theorem exists_pvm_of_unitary (hU : U ∈ unitary (H →L[ℂ] H)) (hinj : ∀ φ, U φ = φ → φ = 0) :
    ∃ P : Set ℝ → (H →L[ℂ] H), IsProjValuedMeasure P ∧ boundedSpectralIntegral P kap = U := by
  refine ⟨PU hU, isPVM_PU hU hinj, ?_⟩
  rw [bsi_eq (isPVM_PU hU hinj) ibb_kap (rep_Phi hU hinj ibb_kap), Phi_kap hU hinj]

end TeschlQM.Spectral.Constr


open MeasureTheory Filter Topology
open scoped ENNReal InnerProductSpace ComplexConjugate

namespace TeschlQM.Spectral.Constr

open TeschlQM.Shared TeschlQM.Spectral TeschlQM.Spectral.Circ TeschlQM.Spectral.BFC

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {P : Set ℝ → (H →L[ℂ] H)}

lemma kap_mem (x : ℝ) : kap x ∈ Metric.sphere (0 : ℂ) 1 := by simpa using norm_kap x

/-- Pull back of a continuous function on the circle along the Cayley map. -/
noncomputable def pb (g : C(Metric.sphere (0 : ℂ) 1, ℂ)) : ℝ → ℂ := fun x => g ⟨kap x, kap_mem x⟩

lemma ibb_pb (g : C(Metric.sphere (0 : ℂ) 1, ℂ)) : IsBoundedBorel (pb g) := by
  refine ⟨(g.continuous.comp (kap_continuous.subtype_mk kap_mem)).measurable, ‖g‖, fun x => ?_⟩
  exact g.norm_coe_le_norm _

lemma bsi_one (hP : IsProjValuedMeasure P) : boundedSpectralIntegral P (fun _ => (1 : ℂ)) = 1 := by
  have : (fun _ : ℝ => (1 : ℂ)) = Set.univ.indicator 1 := by funext x; simp
  rw [this, bsi_indicator hP MeasurableSet.univ, hP.2.1]

/-- The continuous functional calculus on the circle induced by a projection-valued measure. -/
noncomputable def rho (hP : IsProjValuedMeasure P) :
    C(Metric.sphere (0 : ℂ) 1, ℂ) →⋆ₐ[ℂ] (H →L[ℂ] H) where
  toFun g := boundedSpectralIntegral P (pb g)
  map_one' := by
    have : pb (1 : C(Metric.sphere (0 : ℂ) 1, ℂ)) = fun _ : ℝ => (1 : ℂ) := rfl
    rw [this, bsi_one hP]
  map_mul' f g := by
    have : pb (f * g) = pb f * pb g := rfl
    rw [this, bsi_mul hP (ibb_pb f) (ibb_pb g)]
  map_zero' := by
    have : pb (0 : C(Metric.sphere (0 : ℂ) 1, ℂ)) = (0 : ℂ) • (fun _ : ℝ => (1 : ℂ)) := by
      funext x; simp [pb]
    rw [this, bsi_smul hP _ (isBoundedBorel_const 1)]; simp
  map_add' f g := by
    have : pb (f + g) = pb f + pb g := rfl
    rw [this, bsi_add hP (ibb_pb f) (ibb_pb g)]
  commutes' c := by
    have : pb (algebraMap ℂ C(Metric.sphere (0 : ℂ) 1, ℂ) c) = c • (fun _ : ℝ => (1 : ℂ)) := by
      funext x; simp [pb]
    rw [this, bsi_smul hP _ (isBoundedBorel_const 1), bsi_one hP, Algebra.algebraMap_eq_smul_one]
  map_star' g := by
    have : pb (star g) = star (pb g) := rfl
    try simp only
    rw [this, bsi_star hP (ibb_pb g), ContinuousLinearMap.star_eq_adjoint]

lemma rho_apply (hP : IsProjValuedMeasure P) (g : C(Metric.sphere (0 : ℂ) 1, ℂ)) :
    rho hP g = boundedSpectralIntegral P (pb g) := rfl

lemma rho_continuous (hP : IsProjValuedMeasure P) : Continuous (rho hP) := by
  refine AddMonoidHomClass.continuous_of_bound (rho hP) 2 (fun g => ?_)
  rw [rho_apply]
  exact rep_norm_le hP (fun x => g.norm_coe_le_norm _) (rep_bsi hP (ibb_pb g))

/-- A projection-valued measure on `ℝ` is determined by the bounded operator
`∫ (λ - i)/(λ + i) dP(λ)`. -/
theorem pvm_eq_of_bsi_kap {Q : Set ℝ → (H →L[ℂ] H)} (hP : IsProjValuedMeasure P)
    (hQ : IsProjValuedMeasure Q)
    (h : boundedSpectralIntegral P kap = boundedSpectralIntegral Q kap) :
    ∀ Ω, MeasurableSet Ω → Q Ω = P Ω := by
  have hrho : rho hP = rho hQ := by
    refine ContinuousMap.starAlgHom_ext_map_X (rho_continuous hP) (rho_continuous hQ) ?_
    have : pb (Polynomial.toContinuousMapOnAlgHom (Metric.sphere (0 : ℂ) 1) Polynomial.X) = kap := by
      funext x; simp [pb]
    rw [rho_apply, rho_apply, this, h]
  have hCc : ∀ g : ℝ → ℝ, Continuous g → HasCompactSupport g →
      boundedSpectralIntegral P (fun x => (g x : ℂ)) =
        boundedSpectralIntegral Q (fun x => (g x : ℂ)) := by
    intro g hg hs
    let G : C(Metric.sphere (0 : ℂ) 1, ℂ) :=
      ⟨fun z => lift (fun x => (g x : ℂ)) z,
        ((continuousOn_lift (Complex.continuous_ofReal.comp hg)
          (hs.comp_left Complex.ofReal_zero)).restrict)⟩
    have hG : pb G = fun x => (g x : ℂ) := by
      funext x
      simp [pb, G, lift, kap_ne_one, cay_kap]
    have := congrArg (fun r => r G) hrho
    simp only [rho_apply, hG] at this
    exact this
  intro Ω hΩ
  refine ext_of_inner_self (fun ψ => ?_)
  haveI := spectralMeasure_finite hP ψ
  haveI := spectralMeasure_finite hQ ψ
  rw [rep_indicator hQ hΩ ψ, rep_indicator hP hΩ ψ]
  refine ((goodL_integral (spectralMeasure Q ψ)).ext_Cc (goodL_integral (spectralMeasure P ψ))
    (fun g hg hs => ?_)) _ (isBoundedBorel_indicator hΩ)
  have hgb : IsBoundedBorel (fun x => (g x : ℂ)) := isBoundedBorel_of_isCc (IsCc.ofReal hg hs)
  try simp only
  rw [← rep_bsi hQ hgb ψ, ← rep_bsi hP hgb ψ, hCc g hg hs]

end TeschlQM.Spectral.Constr


open MeasureTheory Filter Topology
open scoped ENNReal InnerProductSpace ComplexConjugate

namespace TeschlQM.Spectral.Constr

open TeschlQM.Shared TeschlQM.Spectral TeschlQM.Spectral.Circ TeschlQM.Spectral.BFC

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {P : Set ℝ → (H →L[ℂ] H)}

lemma uInt_congr (hP : IsProjValuedMeasure P) {f g : ℝ → ℂ} (hf : Measurable f)
    (hg : Measurable g) (h : f = g) : uInt hP hf = uInt hP hg := by
  subst h; rfl

lemma ulim_one (hP : IsProjValuedMeasure P) (ψ : H) : ulim P (fun _ => (1 : ℂ)) ψ = ψ := by
  rw [ulim_of_bdd hP (isBoundedBorel_const 1), bsi_one hP, ContinuousLinearMap.one_apply]

lemma kap_mul_add_I (x : ℝ) : kap x * ((x : ℂ) + Complex.I) = (x : ℂ) - Complex.I := by
  unfold kap
  field_simp [add_I_ne_zero x]

lemma id_mul_one_sub_kap (x : ℝ) :
    (x : ℂ) * (1 - kap x) = Complex.I * (1 + kap x) := by
  unfold kap
  field_simp [add_I_ne_zero x]
  ring

/-- The Cayley transform of `∫ λ dQ` is `∫ (λ - i)/(λ + i) dQ`. -/
lemma bsi_kap_of_cayley (hQ : IsProjValuedMeasure P) {U : H →L[ℂ] H}
    (hU2 : ∀ x : (uInt hQ measurable_id').domain,
      U (uInt hQ measurable_id' x + Complex.I • (x : H)) =
        uInt hQ measurable_id' x - Complex.I • (x : H))
    (hU3 : ∀ φ : H, ∃ x : (uInt hQ measurable_id').domain,
      uInt hQ measurable_id' x + Complex.I • (x : H) = φ) :
    boundedSpectralIntegral P kap = U := by
  ext φ
  obtain ⟨x, rfl⟩ := hU3 φ
  rw [hU2 x, uInt_apply]
  have hx : (x : H) ∈ spectralDomain P (fun x : ℝ => (x : ℂ)) := x.2
  have h1 : (x : H) ∈ spectralDomain P (fun _ => (1 : ℂ)) := mem_spectralDomain_const hQ 1 _
  have hlin : ∀ β : ℂ, ulim P ((1 : ℂ) • (fun x : ℝ => (x : ℂ)) + β • (fun _ => (1 : ℂ))) x =
      ulim P (fun x : ℝ => (x : ℂ)) x + β • (x : H) := by
    intro β
    rw [ulim_lin hQ measurable_id' measurable_const 1 β hx h1, one_smul, ulim_one hQ]
  have hF : (x : H) ∈ spectralDomain P
      ((1 : ℂ) • (fun x : ℝ => (x : ℂ)) + Complex.I • (fun _ => (1 : ℂ))) :=
    mem_spectralDomain_of_le measurable_id' measurable_const (a := 1) (b := 1) zero_le_one
      zero_le_one (fun y => by
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, one_mul, mul_one]
        refine (norm_add_le _ _).trans ?_
        rw [Complex.norm_I]; simp) hx h1
  rw [← hlin Complex.I, bsi_ulim hQ ibb_kap
    (g := (1 : ℂ) • (fun x : ℝ => (x : ℂ)) + Complex.I • (fun _ => (1 : ℂ)))
    ((BFC.measurable_id'.const_smul _).add (measurable_const.const_smul _)) hF]
  have e : kap * ((1 : ℂ) • (fun x : ℝ => (x : ℂ)) + Complex.I • (fun _ => (1 : ℂ))) =
      (1 : ℂ) • (fun x : ℝ => (x : ℂ)) + (-Complex.I) • (fun _ => (1 : ℂ)) := by
    funext y
    simp only [Pi.mul_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, one_mul, mul_one]
    rw [kap_mul_add_I]; ring
  rw [e, hlin (-Complex.I)]
  simp [sub_eq_add_neg]

omit [CompleteSpace H] in
lemma two_I_inv_smul (v : H) : (2 * Complex.I)⁻¹ • ((2 * Complex.I) • v) = v := by
  rw [smul_smul, inv_mul_cancel₀ (by simp), one_smul]

/-- A self-adjoint operator whose Cayley transform is `∫ (λ - i)/(λ + i) dP` equals `∫ λ dP`. -/
lemma eq_uInt_of_cayley {A : H →ₗ.[ℂ] H} (hA : IsSelfAdjoint A) (hP : IsProjValuedMeasure P)
    {U : H →L[ℂ] H} (hPU : boundedSpectralIntegral P kap = U)
    (hU2 : ∀ x : A.domain, U (A x + Complex.I • (x : H)) = A x - Complex.I • (x : H)) :
    A = uInt hP measurable_id' := by
  have key : ∀ x : A.domain, (x : H) ∈ spectralDomain P (fun x : ℝ => (x : ℂ)) ∧
      ulim P (fun x : ℝ => (x : ℂ)) x = A x := by
    intro x
    set φ : H := (2 * Complex.I)⁻¹ • (A x + Complex.I • (x : H)) with hφ
    have hUφ : U φ = (2 * Complex.I)⁻¹ • (A x - Complex.I • (x : H)) := by
      rw [hφ, map_smul, hU2 x]
    set g : ℝ → ℂ := (fun _ => (1 : ℂ)) - kap with hgdef
    have hg : IsBoundedBorel g := ibb_sub (isBoundedBorel_const 1) ibb_kap
    have hbsi : boundedSpectralIntegral P g = 1 - U := by
      rw [hgdef, bsi_sub hP (isBoundedBorel_const 1) ibb_kap, bsi_one hP, hPU]
    have hxφ : ulim P g φ = x := by
      rw [ulim_of_bdd hP hg, hbsi, ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply,
        hUφ, hφ, ← smul_sub]
      have : A x + Complex.I • (x : H) - (A x - Complex.I • (x : H)) =
          (2 * Complex.I) • (x : H) := by
        rw [mul_smul, two_smul]; abel
      rw [this, two_I_inv_smul]
    set k : ℝ → ℂ := Complex.I • ((fun _ => (1 : ℂ)) + kap) with hkdef
    have hk : IsBoundedBorel k := ibb_smul _ (ibb_add (isBoundedBorel_const 1) ibb_kap)
    have hidg : (fun x : ℝ => (x : ℂ)) * g = k := by
      funext y
      simp only [hgdef, hkdef, Pi.mul_apply, Pi.sub_apply, Pi.smul_apply, Pi.add_apply,
        smul_eq_mul]
      exact id_mul_one_sub_kap y
    have hφk : φ ∈ spectralDomain P ((fun x : ℝ => (x : ℂ)) * g) := by
      rw [hidg]; exact mem_spectralDomain_of_bdd hP hk φ
    have hφg : φ ∈ spectralDomain P g := mem_spectralDomain_of_bdd hP hg φ
    refine ⟨?_, ?_⟩
    · rw [← hxφ]; exact (mem_comp_iff hP measurable_id' hg.1 hφg).2 hφk
    · rw [← hxφ, ulim_comp hP measurable_id' hg.1 hφg hφk, hidg, ulim_of_bdd hP hk, hkdef,
        bsi_smul hP _ (ibb_add (isBoundedBorel_const 1) ibb_kap),
        bsi_add hP (isBoundedBorel_const 1) ibb_kap, bsi_one hP, hPU,
        ContinuousLinearMap.smul_apply, ContinuousLinearMap.add_apply,
        ContinuousLinearMap.one_apply, hUφ, hφ, ← smul_add]
      have : A x + Complex.I • (x : H) + (A x - Complex.I • (x : H)) = (2 : ℂ) • A x := by
        rw [two_smul]; abel
      rw [this, smul_smul, smul_smul]
      have : Complex.I * (2 * Complex.I)⁻¹ * 2 = 1 := by
        field_simp
      rw [this, one_smul]
  have hle : A ≤ uInt hP measurable_id' := by
    refine ⟨fun x hx => (key ⟨x, hx⟩).1, fun x y hxy => ?_⟩
    rw [uInt_apply, ← hxy]
    exact (key x).2.symm
  have hsym := uInt_formalAdjoint hP (BFC.measurable_id')
  rw [uInt_congr hP (measurable_star' measurable_id') measurable_id'
    (by funext y; simp)] at hsym
  have hdom : (uInt hP measurable_id').domain ≤ A.domain := by
    intro z hz
    have hz' : z ∈ A.adjoint.domain := by
      refine LinearPMap.mem_adjoint_domain_of_exists z ⟨uInt hP measurable_id' ⟨z, hz⟩,
        fun y => ?_⟩
      rw [hsym ⟨z, hz⟩ ⟨y, hle.1 y.2⟩]
      congr 1
      exact (hle.2 rfl).symm
    rwa [LinearPMap.isSelfAdjoint_def.mp hA] at hz'
  exact LinearPMap.eq_of_le_of_domain_eq hle (le_antisymm hle.1 hdom)

end TeschlQM.Spectral.Constr

open TeschlQM.Spectral TeschlQM.Spectral.Constr TeschlQM.Spectral.BFC TeschlQM.Spectral.Circ TeschlQM.Spectral.Cay

/-- Teschl, p. 96, Theorem 3.7 (Spectral theorem). -/
theorem solution {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (A : H →ₗ.[ℂ] H) (hA : IsSelfAdjoint A) :
    ∃ P : Set ℝ → (H →L[ℂ] H), TeschlQM.Shared.IsProjValuedMeasure P ∧
      A = spectralIntegral P (fun x => (x : ℂ)) ∧
      ∀ Q : Set ℝ → (H →L[ℂ] H), TeschlQM.Shared.IsProjValuedMeasure Q →
        A = spectralIntegral Q (fun x => (x : ℂ)) →
        ∀ Ω : Set ℝ, MeasurableSet Ω → Q Ω = P Ω := by
  obtain ⟨U, hU, hU2, hU3⟩ := exists_cayley hA
  have hinj : ∀ φ, U φ = φ → φ = 0 := by
    intro φ hφ
    obtain ⟨x, rfl⟩ := hU3 φ
    rw [hU2 x] at hφ
    have h2 : (2 * Complex.I) • (x : H) = 0 := by
      rw [mul_smul, two_smul]
      have := congrArg (fun v => A x + Complex.I • (x : H) - v) hφ
      simp only [sub_self] at this
      rw [← this]; abel
    have hx : (x : H) = 0 := by
      rw [← two_I_inv_smul (x : H), h2, smul_zero]
    have hx' : x = 0 := Subtype.ext hx
    rw [hx', LinearPMap.map_zero, ZeroMemClass.coe_zero, smul_zero, add_zero]
  obtain ⟨P, hP, hPU⟩ := exists_pvm_of_unitary hU hinj
  refine ⟨P, hP, ?_, ?_⟩
  · rw [spectralIntegral_eq_uInt hP measurable_id']
    exact eq_uInt_of_cayley hA hP hPU hU2
  · intro Q hQ hAQ Ω hΩ
    rw [spectralIntegral_eq_uInt hQ measurable_id'] at hAQ
    subst hAQ
    have hQU : boundedSpectralIntegral Q kap = U := bsi_kap_of_cayley hQ hU2 hU3
    exact pvm_eq_of_bsi_kap hP hQ (hPU.trans hQU.symm) Ω hΩ

