-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Support21.P17.convex_mixtures_uniform_equivalence
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T05:04:56.224141+00:00
-- url     : https://prove2.me/submissions/5d27a9d5-5b50-41a1-b65b-acff9ac8cf02

import Definitions.Def_QAlgorithms_Papers_Independent_Support21_P17
noncomputable section

open scoped ComplexConjugate ComplexOrder Matrix Kronecker Topology TensorProduct

open Filter

namespace QAlgorithms.Papers.Independent.Support21.P17

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

open QAlgorithms.Papers.Independent.Claimed50.P50 (NoiseSpace completedTensorMap)

open QAlgorithms.Papers.Independent.Next46.P33 (UltraweakTest)

open QAlgorithms.Papers.Independent.Next46.P32 (PositiveKernel)

open QAlgorithms.Papers.Independent.Information100.P50 (M Lin coefficientMap)

end QAlgorithms.Papers.Independent.Support21.P17

end

open QAlgorithms.Papers.Independent.Support21.P17
open QAlgorithms.Papers.Independent.Claimed50.P50 (NoiseSpace completedTensorMap)
open scoped ComplexConjugate
lemma g66j_gram_comb {A : Type*} [CStarAlgebra A] {H : SeparableHilbertSpace}
    (Φ Ψ : A →ₗ[ℂ] HilbertEndomorphism H) (hΦ : GramCompletelyPositive Φ)
    (hΨ : GramCompletelyPositive Ψ) (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    GramCompletelyPositive ((a : ℂ) • Φ + (b : ℂ) • Ψ) := by
  intro n x η
  obtain ⟨h1, h2⟩ := hΦ n x η
  obtain ⟨h3, h4⟩ := hΨ n x η
  simp only [LinearMap.add_apply, LinearMap.smul_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply, inner_add_right, inner_smul_right, Finset.sum_add_distrib,
    ← Finset.mul_sum] at h1 h2 h3 h4 ⊢
  simp only [Complex.add_im, Complex.add_re, Complex.mul_im, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, add_zero, sub_zero] at h1 h2 h3 h4 ⊢
  constructor
  · rw [h1, h3]; ring
  · positivity

lemma g66j_gram_of_eq {A : Type*} [CStarAlgebra A] {H : SeparableHilbertSpace}
    (X Φ Ψ : A →ₗ[ℂ] HilbertEndomorphism H) (hΦ : GramCompletelyPositive Φ)
    (hΨ : GramCompletelyPositive Ψ) (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hX : X = (a : ℂ) • Φ + (b : ℂ) • Ψ) : GramCompletelyPositive X := by
  rw [hX]; exact g66j_gram_comb Φ Ψ hΦ hΨ a b ha hb

theorem solution (H K : SeparableHilbertSpace) :
    (∀ (S1 S2 : HilbertEndomorphism H →ₗ[ℂ] HilbertEndomorphism K), IsUnitalNormalCP S1 → IsUnitalNormalCP S2 →
      ∀ l r : ℝ, 0 < l → l < 1 → 0 < r → r < 1 →
      let T := (l : ℂ) • S1 + ((1 - l : ℝ) : ℂ) • S2
      let U := (r : ℂ) • S1 + ((1 - r : ℝ) : ℂ) • S2
      1 < (l * (1 - l))⁻¹ ∧ 1 < (r * (1 - r))⁻¹ ∧
      CompletelyDominated U ((((l * (1 - l))⁻¹ : ℝ) : ℂ) • T) ∧
      CompletelyDominated T ((((r * (1 - r))⁻¹ : ℝ) : ℂ) • U) ∧ UniformlyEquivalent T U) ∧
    Equivalence (fun S T : {T : HilbertEndomorphism H →ₗ[ℂ] HilbertEndomorphism K //
      IsNormalCP (StarAlgHom.id ℂ (HilbertEndomorphism H)) T} => UniformlyEquivalent S.val T.val) := by
  -- key domination lemma
  have dom : ∀ (S1 S2 : HilbertEndomorphism H →ₗ[ℂ] HilbertEndomorphism K),
      GramCompletelyPositive S1 → GramCompletelyPositive S2 →
      ∀ l r : ℝ, 0 < l → l < 1 → 0 < r → r < 1 →
      CompletelyDominated ((r : ℂ) • S1 + ((1 - r : ℝ) : ℂ) • S2)
        ((((l * (1 - l))⁻¹ : ℝ) : ℂ) • ((l : ℂ) • S1 + ((1 - l : ℝ) : ℂ) • S2)) := by
    intro S1 S2 h1 h2 l r hl0 hl1 hr0 hr1
    have h1l : (0:ℝ) < 1 - l := by linarith
    have ea : (l * (1 - l))⁻¹ * l = (1 - l)⁻¹ := by field_simp
    have eb : (l * (1 - l))⁻¹ * (1 - l) = l⁻¹ := by field_simp
    have ga : 1 < (1 - l)⁻¹ := by rw [lt_inv_comm₀ one_pos h1l]; simp; linarith
    have gb : 1 < l⁻¹ := by rw [lt_inv_comm₀ one_pos hl0]; simp; linarith
    apply g66j_gram_of_eq _ S1 S2 h1 h2 ((1 - l)⁻¹ - r) (l⁻¹ - (1 - r)) (by linarith) (by linarith)
    rw [← ea, ← eb]
    simp only [smul_add, smul_smul, Complex.ofReal_sub, Complex.ofReal_mul, Complex.ofReal_one]
    module
  have gt : ∀ l : ℝ, 0 < l → l < 1 → 1 < (l * (1 - l))⁻¹ := by
    intro l h0 h1
    rw [lt_inv_comm₀ one_pos (by nlinarith)]; simp; nlinarith
  constructor
  · intro S1 S2 hS1 hS2 l r hl0 hl1 hr0 hr1
    refine ⟨gt l hl0 hl1, gt r hr0 hr1, dom S1 S2 hS1.1.1 hS2.1.1 l r hl0 hl1 hr0 hr1,
      dom S1 S2 hS1.1.1 hS2.1.1 r l hr0 hr1 hl0 hl1, ?_⟩
    exact ⟨_, _, gt r hr0 hr1, gt l hl0 hl1, dom S1 S2 hS1.1.1 hS2.1.1 r l hr0 hr1 hl0 hl1,
      dom S1 S2 hS1.1.1 hS2.1.1 l r hl0 hl1 hr0 hr1⟩
  · -- (c • T) - S domination combos
    have self : ∀ T : HilbertEndomorphism H →ₗ[ℂ] HilbertEndomorphism K,
        GramCompletelyPositive T → CompletelyDominated T (((2 : ℝ) : ℂ) • T) := by
      intro T hT
      apply g66j_gram_of_eq _ T T hT hT 1 0 (by norm_num) le_rfl
      simp only [Complex.ofReal_one, Complex.ofReal_zero, Complex.ofReal_ofNat]
      module
    have trans : ∀ S T U : HilbertEndomorphism H →ₗ[ℂ] HilbertEndomorphism K, ∀ c c' : ℝ,
        1 < c → 1 < c' → CompletelyDominated S ((c : ℂ) • T) →
        CompletelyDominated T ((c' : ℂ) • U) → CompletelyDominated S (((c * c' : ℝ)) • U) := by
      intro S T U c c' hc hc' h1 h2
      apply g66j_gram_of_eq _ _ _ h2 h1 c 1 (by linarith) zero_le_one
      simp only [Complex.ofReal_one, Complex.ofReal_mul, smul_sub, smul_smul, one_smul]
      module
    refine ⟨fun S => ⟨2, 2, by norm_num, by norm_num, self _ S.2.1, self _ S.2.1⟩,
      fun ⟨c, d, hc, hd, h1, h2⟩ => ⟨d, c, hd, hc, h2, h1⟩, ?_⟩
    rintro S T U ⟨c, d, hc, hd, h1, h2⟩ ⟨c', d', hc', hd', h3, h4⟩
    refine ⟨c * c', d' * d, by nlinarith, by nlinarith, trans _ _ _ c c' hc hc' h1 h3,
      trans _ _ _ d' d hd' hd h4 h2⟩
