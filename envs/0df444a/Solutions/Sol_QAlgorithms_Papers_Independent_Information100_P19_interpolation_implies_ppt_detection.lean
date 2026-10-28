-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Information100.P19.interpolation_implies_ppt_detection
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T10:17:07.678483+00:00
-- url     : https://prove2.me/submissions/2ee28ab7-c0cc-4044-bc2e-00468f48a66b

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P19
noncomputable section

open scoped BigOperators ENNReal Matrix ComplexConjugate ComplexOrder

open Filter MeasureTheory

namespace QAlgorithms.Papers.Independent.Information100.P19

lemma IPD_cyc : cycle4 0 = 1 ∧ cycle4 1 = 2 ∧ cycle4 2 = 3 ∧ cycle4 3 = 0 ∧
  cycle4⁻¹ 0 = 3 ∧ cycle4⁻¹ 1 = 0 ∧ cycle4⁻¹ 2 = 1 ∧ cycle4⁻¹ 3 = 2 := by decide
lemma IPD_ab : alphaPerm 2 (0 : Fin 4) = 3 ∧ alphaPerm 2 (1 : Fin 4) = 2 ∧ alphaPerm 2 (2 : Fin 4) = 1 ∧
  alphaPerm 2 (3 : Fin 4) = 0 ∧ betaPerm 2 (0 : Fin 4) = 1 ∧ betaPerm 2 (1 : Fin 4) = 0 ∧
  betaPerm 2 (2 : Fin 4) = 3 ∧ betaPerm 2 (3 : Fin 4) = 2 := by decide

lemma IPD_prod4 (f : Fin 4 → ℂ) : ∏ r, f r = f 0 * f 1 * f 2 * f 3 := Fin.prod_univ_four f

lemma IPD_trace4 {a b : ℕ} (X : Bip a b) :
    Matrix.trace ((transposeB X)^4) = tensorTrace (cycle4, cycle4⁻¹) X := by
  obtain ⟨c0, c1, c2, c3, d0, d1, d2, d3⟩ := IPD_cyc
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
  simp only [IPD_prod4, c0, c1, c2, c3, d0, d1, d2, d3]

lemma IPD_rmom {a b : ℕ} (X : Bip a b) (hH : X.IsHermitian) :
    Matrix.trace ((realign X * (realign X).conjTranspose)^2) = tensorTrace (alphaPerm 2, betaPerm 2) X := by
  obtain ⟨c0, c1, c2, c3, d0, d1, d2, d3⟩ := IPD_ab
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
  rw [IPD_prod4]
  simp only [c0, c1, c2, c3, d0, d1, d2, d3, hH.apply]
  ring

/-- Four-index contraction of the Gram factor. -/
def IPD_Q {a b : ℕ} (B : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ) (κ : Fin 4 → Fin a × Fin b) : ℂ :=
  ∑ x : Fin a × Fin b × Fin a × Fin b, star (B (κ 0) (x.1, x.2.1)) * B (κ 1) (x.2.2.1, x.2.1) *
    star (B (κ 2) (x.2.2.1, x.2.2.2)) * B (κ 3) (x.1, x.2.2.2)

lemma IPD_expand {n a b : ℕ} (B : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ) (p : Perms n) :
    tensorTrace p (star B * B) = ∑ κ : Fin n → Fin a × Fin b, ∑ i : Fin n → Fin a, ∑ j : Fin n → Fin b,
      ∏ r, star (B (κ r) (i r, j r)) * B (κ r) (i (p.1 r), j (p.2 r)) := by
  unfold tensorTrace
  simp only [Matrix.mul_apply, Matrix.star_apply]
  simp_rw [Finset.prod_univ_sum, Fintype.piFinset_univ]
  rw [Finset.sum_congr rfl (fun i _ => Finset.sum_comm)]
  rw [Finset.sum_comm]

lemma IPD_cycQ {a b : ℕ} (B : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ) (κ : Fin 4 → Fin a × Fin b) :
    ∑ i : Fin 4 → Fin a, ∑ j : Fin 4 → Fin b,
      ∏ r, star (B (κ r) (i r, j r)) * B (κ r) (i (cycle4 r), j (cycle4⁻¹ r)) =
    IPD_Q B κ * IPD_Q B (fun r => κ (cycle4 r)) := by
  obtain ⟨c0, c1, c2, c3, d0, d1, d2, d3⟩ := IPD_cyc
  rw [IPD_Q, IPD_Q, Finset.sum_mul_sum, ← Fintype.sum_prod_type', ← Fintype.sum_prod_type']
  refine Fintype.sum_bijective
    (fun ij : (Fin 4 → Fin a) × (Fin 4 → Fin b) =>
      ((ij.1 0, ij.2 0, ij.1 2, ij.2 2), (ij.1 1, ij.2 1, ij.1 3, ij.2 3)))
    (Function.bijective_iff_has_inverse.mpr ⟨fun q =>
      (![q.1.1, q.2.1, q.1.2.2.1, q.2.2.2.1], ![q.1.2.1, q.2.2.1, q.1.2.2.2, q.2.2.2.2]),
      fun ij => by
        rcases ij with ⟨i, j⟩
        refine Prod.ext ?_ ?_ <;> (ext r; fin_cases r <;> rfl), fun q => rfl⟩) _ _ (fun ij => ?_)
  rcases ij with ⟨i, j⟩
  simp only [IPD_prod4, c0, c1, c2, c3, d0, d1, d2, d3]
  ring

lemma IPD_abQ {a b : ℕ} (B : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ) (κ : Fin 4 → Fin a × Fin b) :
    ∑ i : Fin 4 → Fin a, ∑ j : Fin 4 → Fin b,
      ∏ r : Fin 4, star (B (κ r) (i r, j r)) * B (κ r) (i (alphaPerm 2 r), j (betaPerm 2 r)) =
    IPD_Q B κ * star (IPD_Q B κ) := by
  obtain ⟨c0, c1, c2, c3, d0, d1, d2, d3⟩ := IPD_ab
  rw [IPD_Q]
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
  simp only [IPD_prod4, c0, c1, c2, c3, d0, d1, d2, d3]
  ring

lemma IPD_ineq {a b : ℕ} (B : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ) :
    (tensorTrace (cycle4, cycle4⁻¹) (star B * B)).re ≤
      (tensorTrace (alphaPerm 2, betaPerm 2) (star B * B)).re := by
  rw [IPD_expand, IPD_expand]
  rw [Finset.sum_congr rfl (fun κ _ => IPD_cycQ B κ)]
  rw [Finset.sum_congr rfl (fun κ _ => IPD_abQ B κ)]
  simp only [Complex.re_sum]
  have hre : ∀ z : ℂ, (z * star z).re = ‖z‖ ^ 2 := fun z => by
    rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]; norm_cast
  simp only [hre]
  have h1 : ∀ κ : Fin 4 → Fin a × Fin b, (IPD_Q B κ * IPD_Q B (fun r => κ (cycle4 r))).re ≤
      (‖IPD_Q B κ‖ ^ 2 + ‖IPD_Q B (fun r => κ (cycle4 r))‖ ^ 2) / 2 := fun κ => by
    have h := Complex.re_le_norm (IPD_Q B κ * IPD_Q B (fun r => κ (cycle4 r)))
    rw [norm_mul] at h
    nlinarith [sq_nonneg (‖IPD_Q B κ‖ - ‖IPD_Q B (fun r => κ (cycle4 r))‖)]
  have h2 : ∑ κ : Fin 4 → Fin a × Fin b, ‖IPD_Q B (fun r => κ (cycle4 r))‖ ^ 2 =
      ∑ κ : Fin 4 → Fin a × Fin b, ‖IPD_Q B κ‖ ^ 2 :=
    Fintype.sum_bijective (fun κ : Fin 4 → Fin a × Fin b => fun r => κ (cycle4 r))
      (Function.bijective_iff_has_inverse.mpr ⟨fun κ r => κ (cycle4⁻¹ r),
        fun κ => by funext r; simp, fun κ => by funext r; simp⟩) _ _ (fun κ => rfl)
  calc _ ≤ ∑ κ : Fin 4 → Fin a × Fin b,
        (‖IPD_Q B κ‖ ^ 2 + ‖IPD_Q B (fun r => κ (cycle4 r))‖ ^ 2) / 2 :=
        Finset.sum_le_sum (fun κ _ => h1 κ)
    _ = _ := by rw [← Finset.sum_div, Finset.sum_add_distrib, h2]; ring

open scoped MatrixOrder in
lemma IPD_fact {K : Type*} [Fintype K] [DecidableEq K] {X : Matrix K K ℂ} (hX : X.PosSemidef) :
    ∃ B : Matrix K K ℂ, X = star B * B :=
  CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hX.nonneg

lemma IPD_main {a b : ℕ} (X : Bip a b) (hX : X.PosSemidef) :
    powerTrace (transposeB X) 4 = (tensorTrace (cycle4, cycle4⁻¹) X).re ∧
    rMoment X 2 = (tensorTrace (alphaPerm 2, betaPerm 2) X).re ∧
    (tensorTrace (cycle4, cycle4⁻¹) X).re ≤ (tensorTrace (alphaPerm 2, betaPerm 2) X).re := by
  refine ⟨?_, ?_, ?_⟩
  · unfold powerTrace; rw [IPD_trace4]
  · unfold rMoment powerTrace; rw [IPD_rmom X hX.1]
  · obtain ⟨B, rfl⟩ := IPD_fact hX
    exact IPD_ineq B


lemma IPD_normsum {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] (M : Matrix I J ℂ) :
    ((M * Mᴴ).trace).re = ∑ x : I × J, ‖M x.1 x.2‖ ^ 2 := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Complex.re_sum, ← Fintype.sum_prod_type']
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]; norm_cast

lemma IPD_trle {I : Type*} [Fintype I] [DecidableEq I] (M N : Matrix I I ℂ) (hN : N.IsHermitian) :
    ((M * N).trace).re ≤ ∑ x : I × I, ‖M x.1 x.2‖ * ‖N x.1 x.2‖ := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Complex.re_sum, ← Fintype.sum_prod_type']
  refine Finset.sum_le_sum fun x _ => ?_
  rw [← hN.apply x.1 x.2, norm_star, ← norm_mul]
  exact Complex.re_le_norm _

lemma IPD_herm {a b : ℕ} (X : Bip a b) (hX : X.IsHermitian) : (transposeB X).IsHermitian := by
  ext p q
  simp only [Matrix.conjTranspose_apply, transposeB]
  exact hX.apply (p.1, q.2) (q.1, p.2)

lemma IPD_r1 {a b : ℕ} (X : Bip a b) :
    rMoment X 1 = ((transposeB X * (transposeB X)ᴴ).trace).re := by
  rw [rMoment, powerTrace, pow_one, IPD_normsum, IPD_normsum]
  refine Fintype.sum_equiv
    { toFun := fun x => ((x.1.1, x.2.2), (x.1.2, x.2.1))
      invFun := fun y => ((y.1.1, y.2.1), (y.2.2, y.1.2))
      left_inv := fun x => rfl
      right_inv := fun y => rfl } _ _ (fun x => rfl)

lemma IPD_part1 {a b : ℕ} (X : Bip a b) (hX : X.PosSemidef) :
    rMoment X 1 ^ 2 ≤ powerTrace (transposeB X) 3 → rMoment X 1 ^ 3 ≤ rMoment X 2 := by
  intro h
  set A := transposeB X with hA
  have hH : A.IsHermitian := IPD_herm X hX.1
  have hH2 : (A ^ 2).IsHermitian := hH.pow 2
  obtain ⟨h1, h2, h3⟩ := IPD_main X hX
  have ht4 : powerTrace A 4 ≤ rMoment X 2 := by rw [h1, h2]; exact h3
  have hP : rMoment X 1 = ∑ x : (Fin a × Fin b) × (Fin a × Fin b), ‖A x.1 x.2‖ ^ 2 := by
    rw [IPD_r1, IPD_normsum]
  have hT4 : powerTrace A 4 = ∑ x : (Fin a × Fin b) × (Fin a × Fin b), ‖(A^2) x.1 x.2‖ ^ 2 := by
    rw [← IPD_normsum, hH2.eq, powerTrace, ← pow_add]
  have hT3 : powerTrace A 3 ≤ ∑ x : (Fin a × Fin b) × (Fin a × Fin b), ‖A x.1 x.2‖ * ‖(A^2) x.1 x.2‖ := by
    rw [powerTrace, pow_succ']
    exact IPD_trle A (A ^ 2) hH2
  have hCS := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun x : (Fin a × Fin b) × (Fin a × Fin b) => ‖A x.1 x.2‖)
    (fun x => ‖(A^2) x.1 x.2‖)
  rw [← hP, ← hT4] at hCS
  set P := rMoment X 1
  set S := ∑ x : (Fin a × Fin b) × (Fin a × Fin b), ‖A x.1 x.2‖ * ‖(A^2) x.1 x.2‖
  have hP0 : 0 ≤ P := by rw [hP]; positivity
  have hT40 : 0 ≤ powerTrace A 4 := by rw [hT4]; positivity
  have h4 : P ^ 4 ≤ P * rMoment X 2 := by
    have : P ^ 2 ≤ S := le_trans h hT3
    have hs : (P^2)^2 ≤ S^2 := pow_le_pow_left₀ (by positivity) this 2
    nlinarith
  rcases hP0.lt_or_eq with hp | hp
  · nlinarith [pow_pos hp 3]
  · rw [← hp]; norm_num; linarith

def IPD_J : Matrix (Fin 3 × Fin 3) (Fin 3 × Fin 3) ℂ :=
  Matrix.of fun i j => if i.1 = i.2 ∧ j.1 = j.2 then 1 else 0

def IPD_S : Matrix (Fin 3 × Fin 3) (Fin 3 × Fin 3) ℂ :=
  Matrix.of fun p q => if p.1 = q.2 ∧ q.1 = p.2 then 1 else 0

lemma IPD_mul {I : Type*} [Fintype I] [DecidableEq I] (J : Matrix I I ℂ) (k m α β γ δ : ℂ)
    (hJ : J * J = k • J + m • 1) :
    (α • J + β • 1) * (γ • J + δ • 1) = (α*γ*k + α*δ + β*γ) • J + (α*γ*m + β*δ) • 1 := by
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, hJ,
    Matrix.one_mul, Matrix.mul_one, smul_add, smul_smul]
  module

lemma IPD_JJ : IPD_J * IPD_J = (3:ℂ) • IPD_J + (0:ℂ) • 1 := by
  ext ⟨i1, i2⟩ ⟨j1, j2⟩
  fin_cases i1 <;> fin_cases i2 <;> fin_cases j1 <;> fin_cases j2 <;>
    simp [IPD_J, Matrix.mul_apply, Fintype.sum_prod_type]

lemma IPD_SS : IPD_S * IPD_S = (0:ℂ) • IPD_S + (1:ℂ) • 1 := by
  ext ⟨i1, i2⟩ ⟨j1, j2⟩
  fin_cases i1 <;> fin_cases i2 <;> fin_cases j1 <;> fin_cases j2 <;>
    simp [IPD_S, Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_three]

lemma IPD_trJ : IPD_J.trace = 3 := by
  rw [Matrix.trace]
  simp only [Fintype.sum_prod_type, Fin.sum_univ_three, Matrix.diag, IPD_J, Matrix.of_apply]
  simp [Fin.ext_iff]; norm_num

lemma IPD_trS : IPD_S.trace = 3 := by
  rw [Matrix.trace]
  simp only [Fintype.sum_prod_type, Fin.sum_univ_three, Matrix.diag, IPD_S, Matrix.of_apply]
  simp [Fin.ext_iff]; norm_num

lemma IPD_tr (J : Matrix (Fin 3 × Fin 3) (Fin 3 × Fin 3) ℂ) (hJ : J.trace = 3) (x y : ℂ) :
    (x • J + y • 1).trace = x * 3 + y * 9 := by
  rw [Matrix.trace_add, Matrix.trace_smul, Matrix.trace_smul, hJ, Matrix.trace_one]
  simp

lemma IPD_phi (i j : Fin 3 × Fin 3) :
    phi3 i * conj (phi3 j) = if i.1 = i.2 ∧ j.1 = j.2 then (1/3 : ℂ) else 0 := by
  have h3 : ((Real.sqrt 3 : ℂ))⁻¹ * ((Real.sqrt 3 : ℂ))⁻¹ = 1/3 := by
    rw [← mul_inv, ← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]; norm_num
  simp only [phi3]
  split_ifs <;> simp_all [map_inv₀, Complex.conj_ofReal]

lemma IPD_ent (p q : Fin 3 × Fin 3) : isotropic3 (3/10) p q =
    (if p.1 = p.2 ∧ q.1 = q.2 then (1/10 : ℂ) else 0) + (if p = q then (7/90 : ℂ) else 0) := by
  simp only [isotropic3, Matrix.add_apply, Matrix.smul_apply, outer, smul_eq_mul, IPD_phi,
    Matrix.one_apply]
  push_cast
  split_ifs <;> norm_num

lemma IPD_R : realign (isotropic3 (3/10)) = (7/90 : ℂ) • IPD_J + (1/10 : ℂ) • 1 := by
  ext ⟨i1, i2⟩ ⟨j1, j2⟩
  simp only [realign, IPD_ent, Matrix.add_apply, Matrix.smul_apply, IPD_J, Matrix.of_apply,
    Matrix.one_apply, Prod.mk.injEq, smul_eq_mul]
  split_ifs <;> simp_all; ring

lemma IPD_T : transposeB (isotropic3 (3/10)) = (1/10 : ℂ) • IPD_S + (7/90 : ℂ) • 1 := by
  ext ⟨i1, i2⟩ ⟨j1, j2⟩
  simp only [transposeB, IPD_ent, Matrix.add_apply, Matrix.smul_apply, IPD_S, Matrix.of_apply,
    Matrix.one_apply, Prod.mk.injEq, smul_eq_mul]
  fin_cases i1 <;> fin_cases i2 <;> fin_cases j1 <;> fin_cases j2 <;> norm_num

lemma IPD_RH : (realign (isotropic3 (3/10)))ᴴ = realign (isotropic3 (3/10)) := by
  rw [IPD_R]
  ext i j
  simp only [Matrix.conjTranspose_apply, Matrix.add_apply, Matrix.smul_apply, IPD_J,
    Matrix.of_apply, Matrix.one_apply, smul_eq_mul]
  by_cases h1 : i.1 = i.2 <;> by_cases h2 : j.1 = j.2 <;> by_cases h3 : i = j <;>
    simp [h1, h2, h3, eq_comm (a := j)]

lemma IPD_t3 : powerTrace (transposeB (isotropic3 (3/10))) 3 = 3069/91125 := by
  rw [powerTrace, IPD_T, pow_succ', sq, IPD_mul _ _ _ _ _ _ _ IPD_SS,
    IPD_mul _ _ _ _ _ _ _ IPD_SS, IPD_tr _ IPD_trS]
  norm_num

lemma IPD_m1 : rMoment (isotropic3 (3/10)) 1 = 43/225 := by
  rw [rMoment, powerTrace, IPD_RH, pow_one, IPD_R, IPD_mul _ _ _ _ _ _ _ IPD_JJ, IPD_tr _ IPD_trJ]
  norm_num

lemma IPD_m2 : rMoment (isotropic3 (3/10)) 2 = 10648/810000 := by
  rw [rMoment, powerTrace, IPD_RH, IPD_R, IPD_mul _ _ _ _ _ _ _ IPD_JJ, sq,
    IPD_mul _ _ _ _ _ _ _ IPD_JJ, IPD_tr _ IPD_trJ]
  norm_num

lemma IPD_psd : (isotropic3 (3/10)).PosSemidef := by
  have h : outer phi3 = Matrix.vecMulVec phi3 (star phi3) := by
    ext i j; simp [outer, Matrix.vecMulVec_apply]
  unfold isotropic3
  rw [h]
  exact ((Matrix.posSemidef_vecMulVec_self_star phi3).smul
    (Complex.zero_le_real.mpr (by norm_num))).add
    (Matrix.PosSemidef.one.smul (Complex.zero_le_real.mpr (by norm_num)))

lemma IPD_mass : mass (isotropic3 (3/10)) = 1 := by
  simp [mass, powerTrace, Matrix.trace, IPD_ent, Fintype.sum_prod_type, Fin.sum_univ_three]
  norm_num

end QAlgorithms.Papers.Independent.Information100.P19

open QAlgorithms.Papers.Independent.Information100.P19 in
theorem solution  :
    (∀ a b, 0<a → 0<b → ∀ X : Bip a b, X.PosSemidef → mass X=1 →
      (rMoment X 1^2 ≤ powerTrace (transposeB X) 3 → rMoment X 1^3 ≤ rMoment X 2) ∧
      (rMoment X 2 < rMoment X 1^3 → powerTrace (transposeB X) 3 < rMoment X 1^2)) ∧
    (isotropic3 (3/10)).PosSemidef ∧ mass (isotropic3 (3/10))=1 ∧
    powerTrace (transposeB (isotropic3 (3/10))) 3-rMoment (isotropic3 (3/10)) 1^2 = -16/5625 ∧
    rMoment (isotropic3 (3/10)) 2-rMoment (isotropic3 (3/10)) 1^3 = 140461/22781250 := by
  refine ⟨fun a b _ _ X hX _ => ⟨IPD_part1 X hX, fun h => ?_⟩, ?_⟩
  · by_contra hc
    exact absurd (IPD_part1 X hX (not_lt.mp hc)) (not_le.mpr h)
  · refine ⟨IPD_psd, IPD_mass, ?_, ?_⟩
    · rw [IPD_t3, IPD_m1]; norm_num
    · rw [IPD_m2, IPD_m1]; norm_num

end
