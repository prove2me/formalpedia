-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Intake100.P24.decoherence_nonnegative
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-20T15:08:33.150632+00:00
-- url     : https://prove2.me/submissions/f5584b44-3dfa-4411-9428-ebac9f6e8779

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P24
noncomputable section

open scoped Matrix ComplexConjugate ENNReal ComplexOrder Matrix.Norms.L2Operator

open MeasureTheory

open QAlgorithms.Papers.Independent.Dependency50.P49 (traceDual)

open QAlgorithms.Papers.Independent.Information100.P30 (IsPositiveMap)

namespace QAlgorithms.Papers.Independent.Intake100.P24

local instance : MeasurableSpace PolarizationMatrix := borel PolarizationMatrix

local instance : BorelSpace PolarizationMatrix := ⟨rfl⟩


theorem AuxDN_herm_form (x : Fin 2 → ℂ) (M : PolarizationMatrix) :
    star x ⬝ᵥ (((1 / 2 : ℂ) • (M + Mᴴ)) *ᵥ x) = (((star x ⬝ᵥ (M *ᵥ x)).re : ℝ) : ℂ) := by
  apply Complex.ext <;>
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.conjTranspose_apply] <;> ring

theorem AuxDN_pt (x : Fin 2 → ℂ) (V : PolarizationMatrix) (hV : IsScatteringUnitary V) :
    0 ≤ (star x ⬝ᵥ ((1 - V) *ᵥ x)).re := by
  have h1 : (1 / 2 : ℂ) • ((1 - V) + (1 - V)ᴴ) = (1 / 2 : ℂ) • ((1 - V)ᴴ * (1 - V)) := by
    congr 1
    rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, sub_mul, mul_sub, mul_sub, hV.2]
    noncomm_ring
  have hp : ((1 / 2 : ℂ) • ((1 - V)ᴴ * (1 - V))).PosSemidef :=
    (Matrix.posSemidef_conjTranspose_mul_self (1 - V)).smul (by norm_num [Complex.le_def])
  have := hp.re_dotProduct_nonneg x
  rw [← h1, AuxDN_herm_form] at this
  simpa using this

theorem _root_.solution
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {Omega : Type*} [MeasurableSpace Omega] (mu : Measure Omega) [IsFiniteMeasure mu]
    (U : Omega → H ≃ₗᵢ[ℂ] H) (v : H) (hv : ‖v‖ = 1)
    (hint : Integrable (fun w => (1 : ℂ) - inner ℂ v (U w v)) mu)
    (nu : Measure PolarizationMatrix) [IsFiniteMeasure nu]
    (hunit : ∀ᵐ V ∂nu, IsScatteringUnitary V) :
    0 ≤ (∫ w, (1 : ℂ) - inner ℂ v (U w v) ∂mu).re ∧
      let B : PolarizationMatrix := ∫ V, (1 : PolarizationMatrix) - V ∂nu
      (frequencyShift B).IsHermitian ∧ (decoherencePart B).PosSemidef ∧
        B = Complex.I • frequencyShift B + decoherencePart B := by
  refine ⟨?_, ?_⟩
  · have hre := integral_re hint
    simp only [RCLike.re_to_complex] at hre
    rw [← hre]
    refine integral_nonneg fun w => ?_
    show (0:ℝ) ≤ (1 - inner ℂ v (U w v)).re
    have h := re_inner_le_norm (𝕜 := ℂ) v (U w v)
    rw [LinearIsometryEquiv.norm_map, hv] at h
    simp only [Complex.sub_re, Complex.one_re]
    have : RCLike.re (inner ℂ v (U w v)) = (inner ℂ v (U w v)).re := rfl
    rw [this] at h
    linarith
  intro B
  refine ⟨?_, ?_, ?_⟩
  · unfold frequencyShift
    rw [Matrix.IsHermitian, Matrix.conjTranspose_smul, Matrix.conjTranspose_sub,
      Matrix.conjTranspose_conjTranspose]
    have : star (-Complex.I / 2) = Complex.I / 2 := by
      rw [star_div₀, star_neg]; simp
    rw [this, ← neg_sub, smul_neg, ← neg_smul]
    congr 1
    ring
  · rw [Matrix.posSemidef_iff_dotProduct_mulVec]
    refine ⟨?_, fun x => ?_⟩
    · unfold decoherencePart
      rw [Matrix.IsHermitian, Matrix.conjTranspose_smul, Matrix.conjTranspose_add,
        Matrix.conjTranspose_conjTranspose, add_comm]
      congr 1
      simp
    unfold decoherencePart
    rw [AuxDN_herm_form]
    rw [Complex.zero_le_real]
    by_cases hf : Integrable (fun V : PolarizationMatrix => (1 : PolarizationMatrix) - V) nu
    · let L : PolarizationMatrix →ₗ[ℂ] ℂ :=
        { toFun := fun M => star x ⬝ᵥ (M *ᵥ x)
          map_add' := by intro M N; simp only [Matrix.add_mulVec, dotProduct_add]
          map_smul' := by
            intro r M
            first
              | simp only [Matrix.smul_mulVec_assoc, dotProduct_smul, smul_eq_mul, RingHom.id_apply]
              | simp only [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul, RingHom.id_apply] }
      let Lc : PolarizationMatrix →L[ℂ] ℂ := LinearMap.toContinuousLinearMap L
      have hB : star x ⬝ᵥ (B *ᵥ x) = ∫ V, Lc ((1 : PolarizationMatrix) - V) ∂nu :=
        (Lc.integral_comp_comm hf).symm
      have hre := integral_re (Lc.integrable_comp hf)
      simp only [RCLike.re_to_complex] at hre
      rw [hB, ← hre]
      refine integral_nonneg_of_ae ?_
      filter_upwards [hunit] with V hV
      exact AuxDN_pt x V hV
    · have : B = 0 := integral_undef hf
      rw [this]; simp
  · unfold frequencyShift decoherencePart
    rw [smul_smul]
    ext i j
    simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul]
    ring_nf
    rw [Complex.I_sq]
    ring

end QAlgorithms.Papers.Independent.Intake100.P24

end
