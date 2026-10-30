-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Bridge50.P16.gaussianSynthesis
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-29T15:14:42.136053+00:00
-- url     : https://prove2.me/submissions/030c6fe9-1bc8-490b-a272-f7d8722c5b42

import Definitions.Def_QAlgorithms_Papers_Independent_Bridge50_P16
noncomputable section

open Filter MeasureTheory

open scoped BigOperators ENNReal NNReal Matrix ComplexOrder

namespace QAlgorithms.Papers.Independent.Bridge50.P16

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

open QAlgorithms.Papers.Independent.Frontier30.P08 (interleavedSymplecticForm)

theorem s111_omega_transpose (n : ℕ) :
    (interleavedSymplecticForm n).transpose = -interleavedSymplecticForm n := by
  ext ⟨a, s⟩ ⟨b, t⟩
  simp only [Matrix.transpose_apply, Matrix.neg_apply, interleavedSymplecticForm]
  by_cases h : a = b
  · subst h; fin_cases s <;> fin_cases t <;> simp
  · simp [h, Ne.symm h]

theorem s111_omega_sq (n : ℕ) :
    interleavedSymplecticForm n * interleavedSymplecticForm n = -1 := by
  ext ⟨a, s⟩ ⟨b, t⟩
  simp only [Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two, interleavedSymplecticForm,
    Matrix.neg_apply, Matrix.one_apply, Prod.mk.injEq]
  by_cases h : a = b
  · subst h
    rw [Finset.sum_eq_single a]
    · fin_cases s <;> fin_cases t <;> simp
    · intro c _ hc; simp [Ne.symm hc]
    · simp
  · rw [Finset.sum_eq_zero]
    · simp [h]
    · intro c _
      by_cases hc : a = c
      · subst hc; simp [h]
      · simp [hc]

theorem s111_omegaT_omega (n : ℕ) :
    (interleavedSymplecticForm n).transpose * interleavedSymplecticForm n = 1 := by
  rw [s111_omega_transpose, Matrix.neg_mul, s111_omega_sq, neg_neg]

theorem s111_quad {ι : Type*} [Fintype ι] (A B : Matrix ι ι ℝ) (xi : ι → ℝ) :
    (A *ᵥ xi) ⬝ᵥ (B *ᵥ (A *ᵥ xi)) = xi ⬝ᵥ ((A.transpose * B * A) *ᵥ xi) := by
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec xi A.transpose,
    Matrix.vecMul_transpose]

theorem s111_lam {ι : Type*} [Fintype ι] (V W : Matrix ι ι ℝ) :
    ((fun a b => (V a b : ℂ) + Complex.I / 2 * ((W a b : ℝ) : ℂ)) : Matrix ι ι ℂ) =
      V.map Complex.ofRealHom + (Complex.I / 2) • W.map Complex.ofRealHom := by
  ext a b; simp

end QAlgorithms.Papers.Independent.Bridge50.P16

open QAlgorithms.Papers.Independent.Bridge50.P16
open QAlgorithms.Papers.Independent.Frontier30.P08 (interleavedSymplecticForm)

theorem solution {n : ℕ} (hn : 0 < n)
    (E1 E2 : T.Operation (Fin n → ℕ) (Fin n → ℕ))
    (M1 M2 V1 V2 : Matrix (PhaseIndex n) (PhaseIndex n) ℝ)
    (d1 d2 : PhaseIndex n → ℝ)
    (h1 : GaussianSpecification E1 M1 V1 d1)
    (h2 : GaussianSpecification E2 M2 V2 d2) :
    GaussianSpecification (E2 ∘ E1) (M2 * M1)
      (M2 * V1 * M2.transpose + V2) (M2.mulVec d1 + d2) := by
  obtain ⟨c1, hV1, hP1, hX1⟩ := h1
  obtain ⟨c2, hV2, hP2, hX2⟩ := h2
  set Ω := interleavedSymplecticForm n with hΩ
  have hOT : Ω.transpose = -Ω := s111_omega_transpose n
  have hOO : Ω * Ω = -1 := s111_omega_sq n
  have hTO : Ω.transpose * Ω = 1 := s111_omegaT_omega n
  refine ⟨⟨fun X hX => c2.1 _ (c1.1 X hX), ?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · intro X Y hX hY
    simp only [Function.comp_apply]
    rw [c1.2.1 X Y hX hY, c2.2.1 _ _ (c1.1 X hX) (c1.1 Y hY)]
  · intro c X hX
    simp only [Function.comp_apply]
    rw [c1.2.2.1 c X hX, c2.2.2.1 c _ (c1.1 X hX)]
  · intro m rho
    exact c2.2.2.2 m ⟨_, c1.2.2.2 m rho⟩
  · rw [Matrix.transpose_add, Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose,
      hV1, hV2, Matrix.mul_assoc]
  · rw [s111_lam] at hP1 hP2 ⊢
    have key := (hP1.mul_mul_conjTranspose_same (M2.map Complex.ofRealHom)).add hP2
    convert key using 1
    have hct : (M2.map Complex.ofRealHom)ᴴ = M2.transpose.map Complex.ofRealHom := by
      ext a b; simp
    have hW : Ω - M2 * M1 * Ω * (M2 * M1).transpose =
        M2 * (Ω - M1 * Ω * M1.transpose) * M2.transpose + (Ω - M2 * Ω * M2.transpose) := by
      simp only [Matrix.transpose_mul, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc]
      abel
    rw [hct, hW]
    simp only [← RingHom.mapMatrix_apply]
    simp only [map_add, map_mul, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul,
      Matrix.smul_mul, smul_add]
    abel
  · intro X hX xi
    simp only [Function.comp_apply]
    rw [hX2 _ (c1.1 X hX), hX1 X hX, Matrix.mulVec_mulVec]
    have hA : Ω * M1.transpose * Ω.transpose * (Ω * M2.transpose * Ω.transpose) =
        Ω * (M2 * M1).transpose * Ω.transpose := by
      rw [Matrix.transpose_mul]
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc Ω.transpose Ω, hTO, Matrix.one_mul]
    rw [hA, mul_assoc, ← Complex.exp_add]
    congr 2
    set A2 := Ω * M2.transpose * Ω.transpose
    have q : (∑ a, (A2 *ᵥ xi) a * ((Ω * V1 * Ω.transpose) *ᵥ (A2 *ᵥ xi)) a) =
        ∑ a, xi a * ((Ω * (M2 * V1 * M2.transpose) * Ω.transpose) *ᵥ xi) a := by
      change (A2 *ᵥ xi) ⬝ᵥ ((Ω * V1 * Ω.transpose) *ᵥ (A2 *ᵥ xi)) =
        xi ⬝ᵥ ((Ω * (M2 * V1 * M2.transpose) * Ω.transpose) *ᵥ xi)
      rw [s111_quad]
      congr 2
      simp only [A2, Matrix.transpose_mul, Matrix.transpose_transpose]
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc Ω.transpose Ω, hTO, Matrix.one_mul,
        ← Matrix.mul_assoc Ω.transpose Ω, hTO, Matrix.one_mul]
    have l : (∑ a, d1 a * (Ω *ᵥ (A2 *ᵥ xi)) a) = ∑ a, (M2 *ᵥ d1) a * (Ω *ᵥ xi) a := by
      change d1 ⬝ᵥ (Ω *ᵥ (A2 *ᵥ xi)) = (M2 *ᵥ d1) ⬝ᵥ (Ω *ᵥ xi)
      rw [Matrix.mulVec_mulVec]
      have : Ω * A2 = M2.transpose * Ω := by
        simp only [A2]
        rw [hOT, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hOO]
        simp
      rw [this, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]
    have qsum : ∀ (B C : Matrix (PhaseIndex n) (PhaseIndex n) ℝ),
        (∑ a, xi a * ((Ω * (B + C) * Ω.transpose) *ᵥ xi) a) =
          (∑ a, xi a * ((Ω * B * Ω.transpose) *ᵥ xi) a) +
            ∑ a, xi a * ((Ω * C * Ω.transpose) *ᵥ xi) a := by
      intro B C
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [Matrix.mul_add, Matrix.add_mul, Matrix.add_mulVec, Pi.add_apply, mul_add]
    have lsum : (∑ a, (M2 *ᵥ d1 + d2) a * (Ω *ᵥ xi) a) =
        (∑ a, (M2 *ᵥ d1) a * (Ω *ᵥ xi) a) + ∑ a, d2 a * (Ω *ᵥ xi) a := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [Pi.add_apply, add_mul]
    rw [qsum, lsum, q, l]
    push_cast
    ring
