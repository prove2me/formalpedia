-- Prove2me | solution 1 for PettisIntegral.exists_hasComplexPettisIntegral_of_continuous_of_hasCompactSupport
-- status  : ACCEPTED   (prove)
-- author  : @emmgaml
-- created : 2026-11-22T15:52:52.526329+00:00
-- url     : https://prove2.me/submissions/904cc036-d4c1-4a3f-b676-6d43ca1776eb

import Mathlib
import Definitions.Def_PettisIntegral_Basic
import Definitions.Def_PettisIntegral_ComplexMeasure
import Theorems.Thm_PettisIntegral_pettisIntegrable_of_continuous_of_hasCompactSupport

open MeasureTheory

set_option autoImplicit false

namespace Sol_PettisIntegral_exists_hasComplexPettisIntegral_of_continuous_of_hasCompactSupport

open VectorMeasure

theorem regular_of_le_finite_regular {X : Type*} [TopologicalSpace X] [T2Space X]
    [MeasurableSpace X] [BorelSpace X] (μ ν : Measure X) [IsFiniteMeasure ν]
    [ν.Regular] (h : μ ≤ ν) : μ.Regular := by
  have : IsFiniteMeasure μ := isFiniteMeasure_of_le ν h
  have : μ.InnerRegularCompactLTTop := by
    constructor
    intro A hA r hr
    have he : μ A - r ≠ 0 := ne_of_gt (tsub_pos_of_lt hr)
    obtain ⟨K, hKA, hK, hsmall⟩ :=
      hA.1.exists_isCompact_sdiff_lt (μ := ν) (measure_ne_top ν A) he
    refine ⟨K, hKA, hK, ?_⟩
    have hd : μ (A \ K) < μ A - r := lt_of_le_of_lt (h (A \ K)) hsmall
    have hsum : μ A = μ K + μ (A \ K) := by
      simpa [Set.union_eq_right.mpr hKA] using
        (measure_add_sdiff (μ := μ) hK.measurableSet.nullMeasurableSet A).symm
    rw [lt_tsub_iff_right] at hd
    rw [hsum] at hd
    exact (ENNReal.add_lt_add_iff_right (measure_ne_top μ (A \ K))).mp
      (by simpa [add_comm] using hd)
  infer_instance

/-- The four Jordan parts of the real and imaginary parts of a complex measure are dominated by
its total variation. -/
theorem jordan_parts_le_variation {X : Type*} [MeasurableSpace X] (μ : ComplexMeasure X) :
    (ComplexMeasure.re μ).toJordanDecomposition.posPart ≤ μ.variation ∧
    (ComplexMeasure.re μ).toJordanDecomposition.negPart ≤ μ.variation ∧
    (ComplexMeasure.im μ).toJordanDecomposition.posPart ≤ μ.variation ∧
    (ComplexMeasure.im μ).toJordanDecomposition.negPart ≤ μ.variation := by
  have hre : (ComplexMeasure.re μ).totalVariation ≤ μ.variation := by
    rw [SignedMeasure.totalVariation_eq_variation]
    refine variation_le_of_forall_enorm_le (fun A _ => ?_)
    refine le_trans ?_ (enorm_measure_le_variation μ A)
    simp only [ComplexMeasure.re_apply, ← ofReal_norm]
    exact ENNReal.ofReal_le_ofReal (Complex.abs_re_le_norm (μ A))
  have him : (ComplexMeasure.im μ).totalVariation ≤ μ.variation := by
    rw [SignedMeasure.totalVariation_eq_variation]
    refine variation_le_of_forall_enorm_le (fun A _ => ?_)
    refine le_trans ?_ (enorm_measure_le_variation μ A)
    simp only [ComplexMeasure.im_apply, ← ofReal_norm]
    exact ENNReal.ofReal_le_ofReal (Complex.abs_im_le_norm (μ A))
  exact ⟨(Measure.le_add_right le_rfl).trans hre, (Measure.le_add_left le_rfl).trans hre,
    (Measure.le_add_right le_rfl).trans him, (Measure.le_add_left le_rfl).trans him⟩

variable {X E F F' G G' : Type*} [MeasurableSpace X]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup F'] [NormedSpace ℝ F']
  [NormedAddCommGroup G] [NormedSpace ℝ G]
  [NormedAddCommGroup G'] [NormedSpace ℝ G']

theorem integral_eq_of_transpose_eq {μ : VectorMeasure X F} {ν : VectorMeasure X F'}
    {B : E →L[ℝ] F →L[ℝ] G} {C : E →L[ℝ] F' →L[ℝ] G} {f : X → E}
    (hμ : μ.Integrable f) (hν : ν.Integrable f) (h : μ.transpose B = ν.transpose C) :
    ∫ᵛ x, f x ∂[B; μ] = ∫ᵛ x, f x ∂[C; ν] := by
  rw [integral_eq_setToFun_transpose hμ, integral_eq_setToFun_transpose hν]
  simp only [h]

theorem setToFun_comp_left' [CompleteSpace F] [CompleteSpace G] {μ : Measure X}
    {T : Set X → E →L[ℝ] F} {T' : Set X → E →L[ℝ] G} {C C' : ℝ}
    (hT : DominatedFinMeasAdditive μ T C) (hT' : DominatedFinMeasAdditive μ T' C')
    (L : F →L[ℝ] G) (h : ∀ s, MeasurableSet s → μ s < ⊤ → T' s = L.comp (T s)) (f : X → E) :
    setToFun μ T' hT' f = L (setToFun μ T hT f) := by
  by_cases hf : Integrable f μ
  swap
  · rw [setToFun_undef hT hf, setToFun_undef hT' hf, _root_.map_zero]
  refine Integrable.induction (P := fun f => setToFun μ T' hT' f = L (setToFun μ T hT f))
    ?_ ?_ ?_ ?_ hf
  · intro c s hs hμs
    rw [setToFun_indicator_const hT hs hμs.ne, setToFun_indicator_const hT' hs hμs.ne,
      h s hs hμs]
    rfl
  · intro f g _ hf hg hf' hg'
    rw [setToFun_add hT hf hg, setToFun_add hT' hf hg, hf', hg', _root_.map_add]
  · exact isClosed_eq (continuous_setToFun hT') (L.continuous.comp (continuous_setToFun hT))
  · intro f g hfg _ hf'
    rw [← setToFun_congr_ae hT hfg, ← setToFun_congr_ae hT' hfg, hf']

theorem integral_comp_left_of_transpose [CompleteSpace G] [CompleteSpace G']
    {μ : VectorMeasure X F} {B : E →L[ℝ] F →L[ℝ] G} {B' : E →L[ℝ] F →L[ℝ] G'}
    (L : G →L[ℝ] G') (h : ∀ s, μ.transpose B' s = L.comp (μ.transpose B s)) (f : X → E) :
    ∫ᵛ x, f x ∂[B'; μ] = L (∫ᵛ x, f x ∂[B; μ]) := by
  rw [VectorMeasure.integral_eq_setToFun, VectorMeasure.integral_eq_setToFun]
  exact setToFun_comp_left' _ _ L (fun s _ _ => h s) f

/-- `B₁ z r = r • z`. -/
noncomputable abbrev B₁ : ℂ →L[ℝ] ℝ →L[ℝ] ℂ := (ContinuousLinearMap.lsmul ℝ ℝ).flip
/-- multiplication by `I`. -/
noncomputable abbrev mulI : ℂ →L[ℝ] ℂ := (ContinuousLinearMap.mul ℝ ℂ) Complex.I
/-- `B₂ z r = I * (r • z)`. -/
noncomputable abbrev B₂ : ℂ →L[ℝ] ℝ →L[ℝ] ℂ := (ContinuousLinearMap.compL ℝ ℝ ℂ ℂ mulI).comp B₁
/-- evaluation pairing. -/
noncomputable abbrev ev : ℂ →L[ℝ] (ℂ →L[ℝ] ℂ) →L[ℝ] ℂ :=
  (ContinuousLinearMap.id ℝ (ℂ →L[ℝ] ℂ)).flip

theorem transpose_ev (σ : VectorMeasure X (ℂ →L[ℝ] ℂ)) : σ.transpose ev = σ := by
  ext A hA : 1
  rfl

theorem transpose_apply_apply (P : VectorMeasure X F) (B : E →L[ℝ] F →L[ℝ] G) (A : Set X) (z : E) :
    P.transpose B A z = B z (P A) := by
  rfl

theorem integral_B₂ (P : SignedMeasure X) (g : X → ℂ) :
    ∫ᵛ x, g x ∂[B₂; P] = Complex.I * ∫ᵛ x, g x ∂[B₁; P] := by
  rw [integral_comp_left_of_transpose mulI]
  · rfl
  · intro A
    ext z
    simp [transpose_apply_apply]

theorem integrable_transpose_toSignedMeasure (ν : Measure X) [IsFiniteMeasure ν]
    (B : E →L[ℝ] ℝ →L[ℝ] G) {g : X → E}
    (hg : ∀ ρ : Measure X, IsFiniteMeasure ρ → Integrable g ρ) :
    (ν.toSignedMeasure.transpose B).Integrable g :=
  (hg (‖B‖₊ • ν) inferInstance).mono_measure
    ((variation_transpose_le _ _).trans (by rw [Measure.variation_toSignedMeasure]))

theorem integral_mul_eq (μ : ComplexMeasure X) [IsFiniteMeasure μ.variation] (g : X → ℂ)
    (hg : ∀ ρ : Measure X, IsFiniteMeasure ρ → Integrable g ρ) :
    ∫ᵛ x, g x ∂[ContinuousLinearMap.mul ℝ ℂ; μ] =
      (∫ x, g x ∂(ComplexMeasure.re μ).toJordanDecomposition.posPart -
        ∫ x, g x ∂(ComplexMeasure.re μ).toJordanDecomposition.negPart) +
      Complex.I * (∫ x, g x ∂(ComplexMeasure.im μ).toJordanDecomposition.posPart -
        ∫ x, g x ∂(ComplexMeasure.im μ).toJordanDecomposition.negPart) := by
  set j₁ := (ComplexMeasure.re μ).toJordanDecomposition with hj₁
  set j₂ := (ComplexMeasure.im μ).toJordanDecomposition with hj₂
  have hre : ComplexMeasure.re μ = j₁.posPart.toSignedMeasure - j₁.negPart.toSignedMeasure :=
    (SignedMeasure.toSignedMeasure_toJordanDecomposition _).symm
  have him : ComplexMeasure.im μ = j₂.posPart.toSignedMeasure - j₂.negPart.toSignedMeasure :=
    (SignedMeasure.toSignedMeasure_toJordanDecomposition _).symm
  have hτ : μ.transpose (ContinuousLinearMap.mul ℝ ℂ) =
      (j₁.posPart.toSignedMeasure.transpose B₁ - j₁.negPart.toSignedMeasure.transpose B₁) +
      (j₂.posPart.toSignedMeasure.transpose B₂ - j₂.negPart.toSignedMeasure.transpose B₂) := by
    ext A hA : 1
    ext z
    have h1 := congrArg (fun s : SignedMeasure X => s A) hre
    have h2 := congrArg (fun s : SignedMeasure X => s A) him
    simp only [ComplexMeasure.re_apply, ComplexMeasure.im_apply, VectorMeasure.sub_apply] at h1 h2
    simp only [VectorMeasure.add_apply, VectorMeasure.sub_apply, transpose_apply_apply]
    rw [← _root_.map_sub (B₁ z), ← _root_.map_sub (B₂ z), ← h1, ← h2]
    change z * μ A = B₁ z ((μ A).re) + B₂ z ((μ A).im)
    apply Complex.ext <;> simp <;> ring
  have hμi : μ.Integrable g := hg _ inferInstance
  have i₁ := integrable_transpose_toSignedMeasure j₁.posPart B₁ hg
  have i₂ := integrable_transpose_toSignedMeasure j₁.negPart B₁ hg
  have i₃ := integrable_transpose_toSignedMeasure j₂.posPart B₂ hg
  have i₄ := integrable_transpose_toSignedMeasure j₂.negPart B₂ hg
  have hp : ∀ (ν : Measure X) [IsFiniteMeasure ν], ν.toSignedMeasure.Integrable g := by
    intro ν hν
    change Integrable g ν.toSignedMeasure.variation
    rw [Measure.variation_toSignedMeasure]
    exact hg ν hν
  have hτi : (μ.transpose (ContinuousLinearMap.mul ℝ ℂ)).Integrable g := by
    rw [hτ]
    exact (i₁.sub_vectorMeasure i₂).add_vectorMeasure (i₃.sub_vectorMeasure i₄)
  rw [integral_eq_of_transpose_eq (C := ev) hμi hτi (transpose_ev _).symm, hτ,
    integral_add_vectorMeasure (i₁.sub_vectorMeasure i₂) (i₃.sub_vectorMeasure i₄),
    integral_sub_vectorMeasure i₁ i₂, integral_sub_vectorMeasure i₃ i₄,
    integral_eq_of_transpose_eq i₁ (hp _) (transpose_ev _),
    integral_eq_of_transpose_eq i₂ (hp _) (transpose_ev _),
    integral_eq_of_transpose_eq i₃ (hp _) (transpose_ev _),
    integral_eq_of_transpose_eq i₄ (hp _) (transpose_ev _),
    integral_B₂, integral_B₂, integral_toSignedMeasure, integral_toSignedMeasure,
    integral_toSignedMeasure, integral_toSignedMeasure]
  ring

end Sol_PettisIntegral_exists_hasComplexPettisIntegral_of_continuous_of_hasCompactSupport

open PettisIntegral
open Sol_PettisIntegral_exists_hasComplexPettisIntegral_of_continuous_of_hasCompactSupport

theorem solution {E X : Type*}
    [AddCommGroup E] [Module ℂ E] [UniformSpace E] [IsUniformAddGroup E] [ContinuousSMul ℂ E]
    [PolynormableSpace ℂ E] [T2Space E] [QuasiCompleteSpace ℂ E]
    [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X] [MeasurableSpace X] [BorelSpace X]
    (μ : ComplexMeasure X) [IsFiniteMeasure μ.variation] [μ.variation.Regular]
    (f : X → E) (hf : Continuous f) (hc : HasCompactSupport f) :
    ∃ a : E, HasComplexPettisIntegral μ f a := by
  obtain ⟨h₁, h₂, h₃, h₄⟩ := jordan_parts_le_variation μ
  have := regular_of_le_finite_regular _ _ h₁
  have := regular_of_le_finite_regular _ _ h₂
  have := regular_of_le_finite_regular _ _ h₃
  have := regular_of_le_finite_regular _ _ h₄
  obtain ⟨a₁, ha₁⟩ := PettisIntegral.pettisIntegrable_of_continuous_of_hasCompactSupport (𝕜 := ℂ)
    (ComplexMeasure.re μ).toJordanDecomposition.posPart f hf hc
  obtain ⟨a₂, ha₂⟩ := PettisIntegral.pettisIntegrable_of_continuous_of_hasCompactSupport (𝕜 := ℂ)
    (ComplexMeasure.re μ).toJordanDecomposition.negPart f hf hc
  obtain ⟨a₃, ha₃⟩ := PettisIntegral.pettisIntegrable_of_continuous_of_hasCompactSupport (𝕜 := ℂ)
    (ComplexMeasure.im μ).toJordanDecomposition.posPart f hf hc
  obtain ⟨a₄, ha₄⟩ := PettisIntegral.pettisIntegrable_of_continuous_of_hasCompactSupport (𝕜 := ℂ)
    (ComplexMeasure.im μ).toJordanDecomposition.negPart f hf hc
  have hg : ∀ φ : StrongDual ℂ E, ∀ ρ : Measure X, IsFiniteMeasure ρ →
      Integrable (fun x => φ (f x)) ρ := by
    intro φ ρ hρ
    exact (φ.continuous.comp hf).integrable_of_hasCompactSupport (hc.comp_left φ.map_zero)
  refine ⟨(a₁ - a₂) + Complex.I • (a₃ - a₄), fun φ => hg φ _ inferInstance, fun φ => ?_⟩
  rw [complexWeakIntegral_apply, integral_mul_eq μ _ (hg φ), _root_.map_add, _root_.map_sub,
    _root_.map_smul, _root_.map_sub, ha₁.2 φ, ha₂.2 φ, ha₃.2 φ, ha₄.2 φ, smul_eq_mul]
