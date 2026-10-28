-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Information100.P19.fourth_moment_comparison
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T10:03:48.819217+00:00
-- url     : https://prove2.me/submissions/f6e477a1-f425-486b-9498-6cb666699eff

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P19
noncomputable section

open scoped BigOperators ENNReal Matrix ComplexConjugate ComplexOrder

open Filter MeasureTheory

namespace QAlgorithms.Papers.Independent.Information100.P19

lemma FMC_cyc : cycle4 0 = 1 ∧ cycle4 1 = 2 ∧ cycle4 2 = 3 ∧ cycle4 3 = 0 ∧
  cycle4⁻¹ 0 = 3 ∧ cycle4⁻¹ 1 = 0 ∧ cycle4⁻¹ 2 = 1 ∧ cycle4⁻¹ 3 = 2 := by decide
lemma FMC_ab : alphaPerm 2 (0 : Fin 4) = 3 ∧ alphaPerm 2 (1 : Fin 4) = 2 ∧ alphaPerm 2 (2 : Fin 4) = 1 ∧
  alphaPerm 2 (3 : Fin 4) = 0 ∧ betaPerm 2 (0 : Fin 4) = 1 ∧ betaPerm 2 (1 : Fin 4) = 0 ∧
  betaPerm 2 (2 : Fin 4) = 3 ∧ betaPerm 2 (3 : Fin 4) = 2 := by decide

lemma FMC_prod4 (f : Fin 4 → ℂ) : ∏ r, f r = f 0 * f 1 * f 2 * f 3 := Fin.prod_univ_four f

lemma FMC_trace4 {a b : ℕ} (X : Bip a b) :
    Matrix.trace ((transposeB X)^4) = tensorTrace (cycle4, cycle4⁻¹) X := by
  obtain ⟨c0, c1, c2, c3, d0, d1, d2, d3⟩ := FMC_cyc
  simp only [pow_succ, pow_zero, Matrix.one_mul, Matrix.trace, Matrix.diag, Matrix.mul_apply,
    Finset.sum_mul, transposeB]
  simp only [← Fintype.sum_prod_type']
  unfold tensorTrace
  rw [← Fintype.sum_prod_type']
  symm
  refine Fintype.sum_bijective
    (fun ij : (Fin 4 → Fin a) × (Fin 4 → Fin b) =>
      ((ij.1 0, ij.2 3), (ij.1 3, ij.2 2), (ij.1 2, ij.2 1), (ij.1 1, ij.2 0)))
    (Function.bijective_iff_has_inverse.mpr ⟨fun q =>
      (![q.1.1, q.2.2.2.1, q.2.2.1.1, q.2.1.1], ![q.2.2.2.2, q.2.2.1.2, q.2.1.2, q.1.2]),
      fun ij => by
        rcases ij with ⟨i, j⟩
        refine Prod.ext ?_ ?_ <;> (ext r; fin_cases r <;> rfl), fun q => rfl⟩) _ _ (fun ij => ?_)
  rcases ij with ⟨i, j⟩
  simp only [FMC_prod4, c0, c1, c2, c3, d0, d1, d2, d3]

lemma FMC_rmom {a b : ℕ} (X : Bip a b) (hH : X.IsHermitian) :
    Matrix.trace ((realign X * (realign X).conjTranspose)^2) = tensorTrace (alphaPerm 2, betaPerm 2) X := by
  obtain ⟨c0, c1, c2, c3, d0, d1, d2, d3⟩ := FMC_ab
  simp only [sq, Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply, realign,
    Finset.sum_mul_sum]
  simp only [← Fintype.sum_prod_type']
  unfold tensorTrace
  rw [← Fintype.sum_prod_type']
  symm
  refine Fintype.sum_bijective
    (fun ij : (Fin 4 → Fin a) × (Fin 4 → Fin b) =>
      ((ij.1 0, ij.1 3), (ij.1 2, ij.1 1), (ij.2 0, ij.2 1), (ij.2 2, ij.2 3)))
    (Function.bijective_iff_has_inverse.mpr ⟨fun q =>
      (![q.1.1, q.2.1.2, q.2.1.1, q.1.2], ![q.2.2.1.1, q.2.2.1.2, q.2.2.2.1, q.2.2.2.2]),
      fun ij => by
        rcases ij with ⟨i, j⟩
        refine Prod.ext ?_ ?_ <;> (ext r; fin_cases r <;> rfl), fun q => rfl⟩) _ _ (fun ij => ?_)
  rcases ij with ⟨i, j⟩
  rw [FMC_prod4]
  simp only [c0, c1, c2, c3, d0, d1, d2, d3, hH.apply]
  ring

/-- Four-index contraction of the Gram factor. -/
def FMC_Q {a b : ℕ} (B : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ) (κ : Fin 4 → Fin a × Fin b) : ℂ :=
  ∑ x : Fin a × Fin b × Fin a × Fin b, star (B (κ 0) (x.1, x.2.1)) * B (κ 1) (x.2.2.1, x.2.1) *
    star (B (κ 2) (x.2.2.1, x.2.2.2)) * B (κ 3) (x.1, x.2.2.2)

lemma FMC_expand {n a b : ℕ} (B : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ) (p : Perms n) :
    tensorTrace p (star B * B) = ∑ κ : Fin n → Fin a × Fin b, ∑ i : Fin n → Fin a, ∑ j : Fin n → Fin b,
      ∏ r, star (B (κ r) (i r, j r)) * B (κ r) (i (p.1 r), j (p.2 r)) := by
  unfold tensorTrace
  simp only [Matrix.mul_apply, Matrix.star_apply]
  simp_rw [Finset.prod_univ_sum, Fintype.piFinset_univ]
  rw [Finset.sum_congr rfl (fun i _ => Finset.sum_comm)]
  rw [Finset.sum_comm]

lemma FMC_cycQ {a b : ℕ} (B : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ) (κ : Fin 4 → Fin a × Fin b) :
    ∑ i : Fin 4 → Fin a, ∑ j : Fin 4 → Fin b,
      ∏ r, star (B (κ r) (i r, j r)) * B (κ r) (i (cycle4 r), j (cycle4⁻¹ r)) =
    FMC_Q B κ * FMC_Q B (fun r => κ (cycle4 r)) := by
  obtain ⟨c0, c1, c2, c3, d0, d1, d2, d3⟩ := FMC_cyc
  rw [FMC_Q, FMC_Q, Finset.sum_mul_sum, ← Fintype.sum_prod_type', ← Fintype.sum_prod_type']
  refine Fintype.sum_bijective
    (fun ij : (Fin 4 → Fin a) × (Fin 4 → Fin b) =>
      ((ij.1 0, ij.2 0, ij.1 2, ij.2 2), (ij.1 1, ij.2 1, ij.1 3, ij.2 3)))
    (Function.bijective_iff_has_inverse.mpr ⟨fun q =>
      (![q.1.1, q.2.1, q.1.2.2.1, q.2.2.2.1], ![q.1.2.1, q.2.2.1, q.1.2.2.2, q.2.2.2.2]),
      fun ij => by
        rcases ij with ⟨i, j⟩
        refine Prod.ext ?_ ?_ <;> (ext r; fin_cases r <;> rfl), fun q => rfl⟩) _ _ (fun ij => ?_)
  rcases ij with ⟨i, j⟩
  simp only [FMC_prod4, c0, c1, c2, c3, d0, d1, d2, d3]
  ring

lemma FMC_abQ {a b : ℕ} (B : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ) (κ : Fin 4 → Fin a × Fin b) :
    ∑ i : Fin 4 → Fin a, ∑ j : Fin 4 → Fin b,
      ∏ r : Fin 4, star (B (κ r) (i r, j r)) * B (κ r) (i (alphaPerm 2 r), j (betaPerm 2 r)) =
    FMC_Q B κ * star (FMC_Q B κ) := by
  obtain ⟨c0, c1, c2, c3, d0, d1, d2, d3⟩ := FMC_ab
  rw [FMC_Q]
  simp only [star_sum, star_mul', star_star]
  rw [Finset.sum_mul_sum, ← Fintype.sum_prod_type', ← Fintype.sum_prod_type']
  refine Fintype.sum_bijective
    (fun ij : (Fin 4 → Fin a) × (Fin 4 → Fin b) =>
      ((ij.1 0, ij.2 0, ij.1 2, ij.2 2), (ij.1 3, ij.2 1, ij.1 1, ij.2 3)))
    (Function.bijective_iff_has_inverse.mpr ⟨fun q =>
      (![q.1.1, q.2.2.2.1, q.1.2.2.1, q.2.1], ![q.1.2.1, q.2.2.1, q.1.2.2.2, q.2.2.2.2]),
      fun ij => by
        rcases ij with ⟨i, j⟩
        refine Prod.ext ?_ ?_ <;> (ext r; fin_cases r <;> rfl), fun q => rfl⟩) _ _ (fun ij => ?_)
  rcases ij with ⟨i, j⟩
  simp only [FMC_prod4, c0, c1, c2, c3, d0, d1, d2, d3]
  ring

lemma FMC_ineq {a b : ℕ} (B : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ) :
    (tensorTrace (cycle4, cycle4⁻¹) (star B * B)).re ≤
      (tensorTrace (alphaPerm 2, betaPerm 2) (star B * B)).re := by
  rw [FMC_expand, FMC_expand]
  rw [Finset.sum_congr rfl (fun κ _ => FMC_cycQ B κ)]
  rw [Finset.sum_congr rfl (fun κ _ => FMC_abQ B κ)]
  simp only [Complex.re_sum]
  have hre : ∀ z : ℂ, (z * star z).re = ‖z‖ ^ 2 := fun z => by
    rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]; norm_cast
  simp only [hre]
  have h1 : ∀ κ : Fin 4 → Fin a × Fin b, (FMC_Q B κ * FMC_Q B (fun r => κ (cycle4 r))).re ≤
      (‖FMC_Q B κ‖ ^ 2 + ‖FMC_Q B (fun r => κ (cycle4 r))‖ ^ 2) / 2 := fun κ => by
    have h := Complex.re_le_norm (FMC_Q B κ * FMC_Q B (fun r => κ (cycle4 r)))
    rw [norm_mul] at h
    nlinarith [sq_nonneg (‖FMC_Q B κ‖ - ‖FMC_Q B (fun r => κ (cycle4 r))‖)]
  have h2 : ∑ κ : Fin 4 → Fin a × Fin b, ‖FMC_Q B (fun r => κ (cycle4 r))‖ ^ 2 =
      ∑ κ : Fin 4 → Fin a × Fin b, ‖FMC_Q B κ‖ ^ 2 :=
    Fintype.sum_bijective (fun κ : Fin 4 → Fin a × Fin b => fun r => κ (cycle4 r))
      (Function.bijective_iff_has_inverse.mpr ⟨fun κ r => κ (cycle4⁻¹ r),
        fun κ => by funext r; simp, fun κ => by funext r; simp⟩) _ _ (fun κ => rfl)
  calc _ ≤ ∑ κ : Fin 4 → Fin a × Fin b,
        (‖FMC_Q B κ‖ ^ 2 + ‖FMC_Q B (fun r => κ (cycle4 r))‖ ^ 2) / 2 :=
        Finset.sum_le_sum (fun κ _ => h1 κ)
    _ = _ := by rw [← Finset.sum_div, Finset.sum_add_distrib, h2]; ring

open scoped MatrixOrder in
lemma FMC_fact {K : Type*} [Fintype K] [DecidableEq K] {X : Matrix K K ℂ} (hX : X.PosSemidef) :
    ∃ B : Matrix K K ℂ, X = star B * B :=
  CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hX.nonneg

lemma FMC_main {a b : ℕ} (X : Bip a b) (hX : X.PosSemidef) :
    powerTrace (transposeB X) 4 = (tensorTrace (cycle4, cycle4⁻¹) X).re ∧
    rMoment X 2 = (tensorTrace (alphaPerm 2, betaPerm 2) X).re ∧
    (tensorTrace (cycle4, cycle4⁻¹) X).re ≤ (tensorTrace (alphaPerm 2, betaPerm 2) X).re := by
  refine ⟨?_, ?_, ?_⟩
  · unfold powerTrace; rw [FMC_trace4]
  · unfold rMoment powerTrace; rw [FMC_rmom X hX.1]
  · obtain ⟨B, rfl⟩ := FMC_fact hX
    exact FMC_ineq B

lemma FMC_sep_psd {a b : ℕ} {X : Bip a b} (h : QAlgorithms.Entanglement.IsSeparablePositive X) :
    X.PosSemidef := by
  obtain ⟨q, w, A, B, hw, hAB, rfl⟩ := h
  exact Matrix.posSemidef_sum _ (fun j _ =>
    ((hAB j).1.1.kronecker (hAB j).2.1).smul (Complex.zero_le_real.mpr (hw j)))

end QAlgorithms.Papers.Independent.Information100.P19

open QAlgorithms.Papers.Independent.Information100.P19 in
theorem solution  :
    (∀ a b, 0<a → 0<b → ∀ X : Bip a b, X.PosSemidef →
      powerTrace (transposeB X) 4 ≤ rMoment X 2 ∧
      0 ≤ (tensorTrace (alphaPerm 2,betaPerm 2) X).re -
        (tensorTrace (cycle4,cycle4⁻¹) X).re) ∧
    tensorBasis (alphaPerm 2,betaPerm 2)-tensorBasis (cycle4,cycle4⁻¹) ∈ sepCone 4 := by
  refine ⟨fun a b _ _ X hX => ?_, ?_⟩
  · obtain ⟨h1, h2, h3⟩ := FMC_main X hX
    exact ⟨by rw [h1, h2]; exact h3, by linarith⟩
  · intro a b _ _ X hX
    obtain ⟨-, -, h3⟩ := FMC_main X (FMC_sep_psd hX)
    unfold tensorEval
    simp only [Pi.sub_apply, tensorBasis, sub_mul, ite_mul, one_mul, zero_mul,
      Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    linarith

end
