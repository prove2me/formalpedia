-- Prove2me | solution 1 for QMaxCutBeyond.TwoQubit.weighted_eq_15
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-19T05:48:25.631094+00:00
-- url     : https://prove2.me/submissions/425fc71c-3745-45e8-84ac-f58ca1a3bf6b

import Mathlib
import Definitions.Def_QMaxCutBeyond_TwoQubit_Setting

namespace QMaxCutBeyond.TwoQubit

open Matrix

private noncomputable def dotSpin {n : ℕ} (i j : Fin n) : Op n :=
  onSite i pauliX * onSite j pauliX +
  onSite i pauliY * onSite j pauliY +
  onSite i pauliZ * onSite j pauliZ

private lemma pauliX_sq : pauliX * pauliX = 1 := by
  ext a b; fin_cases a <;> fin_cases b <;> simp [pauliX, Matrix.mul_apply, Fin.sum_univ_two]

private lemma pauliY_sq : pauliY * pauliY = 1 := by
  ext a b; fin_cases a <;> fin_cases b <;> simp [pauliY, Matrix.mul_apply, Fin.sum_univ_two]

private lemma pauliZ_sq : pauliZ * pauliZ = 1 := by
  ext a b; fin_cases a <;> fin_cases b <;> simp [pauliZ, Matrix.mul_apply, Fin.sum_univ_two]

private lemma pauliX_mul_pauliY : pauliX * pauliY = Complex.I • pauliZ := by
  ext a b; fin_cases a <;> fin_cases b <;> simp [pauliX, pauliY, pauliZ, Matrix.mul_apply, Fin.sum_univ_two]

private lemma pauliY_mul_pauliX : pauliY * pauliX = (-Complex.I) • pauliZ := by
  ext a b; fin_cases a <;> fin_cases b <;> simp [pauliX, pauliY, pauliZ, Matrix.mul_apply, Fin.sum_univ_two]

private lemma pauliY_mul_pauliZ : pauliY * pauliZ = Complex.I • pauliX := by
  ext a b; fin_cases a <;> fin_cases b <;> simp [pauliX, pauliY, pauliZ, Matrix.mul_apply, Fin.sum_univ_two]

private lemma pauliZ_mul_pauliY : pauliZ * pauliY = (-Complex.I) • pauliX := by
  ext a b; fin_cases a <;> fin_cases b <;> simp [pauliX, pauliY, pauliZ, Matrix.mul_apply, Fin.sum_univ_two]

private lemma pauliZ_mul_pauliX : pauliZ * pauliX = Complex.I • pauliY := by
  ext a b; fin_cases a <;> fin_cases b <;> simp [pauliX, pauliY, pauliZ, Matrix.mul_apply, Fin.sum_univ_two]

private lemma pauliX_mul_pauliZ : pauliX * pauliZ = (-Complex.I) • pauliY := by
  ext a b; fin_cases a <;> fin_cases b <;> simp [pauliX, pauliY, pauliZ, Matrix.mul_apply, Fin.sum_univ_two]

private lemma pauliX_herm : pauliXᴴ = pauliX := by
  ext a b; fin_cases a <;> fin_cases b <;> simp [pauliX, Matrix.conjTranspose_apply]

private lemma pauliY_herm : pauliYᴴ = pauliY := by
  ext a b; fin_cases a <;> fin_cases b <;> simp [pauliY, Matrix.conjTranspose_apply]

private lemma pauliZ_herm : pauliZᴴ = pauliZ := by
  ext a b; fin_cases a <;> fin_cases b <;> simp [pauliZ, Matrix.conjTranspose_apply]

private noncomputable def tensorOpGen {n : ℕ} (A : Fin n → Matrix (Fin 2) (Fin 2) ℂ) : Op n :=
  fun x y => ∏ k : Fin n, A k (x k) (y k)

private lemma tensorOpGen_mul {n : ℕ} (A B : Fin n → Matrix (Fin 2) (Fin 2) ℂ) :
    tensorOpGen A * tensorOpGen B = tensorOpGen (fun k => A k * B k) := by
  ext x z
  simp only [tensorOpGen, Matrix.mul_apply]
  have h1 : ∀ y : Config n,
      (∏ k : Fin n, A k (x k) (y k)) * (∏ k : Fin n, B k (y k) (z k)) =
      ∏ k : Fin n, (A k (x k) (y k) * B k (y k) (z k)) := fun y => (Finset.prod_mul_distrib).symm
  simp_rw [h1]
  exact (Fintype.prod_sum (fun k b => A k (x k) b * B k b (z k))).symm

private lemma tensorOpGen_one {n : ℕ} : tensorOpGen (fun _ : Fin n => (1 : Matrix (Fin 2) (Fin 2) ℂ)) = 1 := by
  ext x y
  simp only [tensorOpGen, Matrix.one_apply]
  by_cases hxy : x = y
  · subst hxy; simp
  · rw [if_neg hxy]
    have hex : ∃ k : Fin n, x k ≠ y k := by
      by_contra h; push Not at h; exact hxy (funext h)
    rcases hex with ⟨k, hk⟩
    exact Finset.prod_eq_zero (Finset.mem_univ k) (by simp [hk])

private lemma onSite_eq_tensorOpGen {n : ℕ} (i : Fin n) (A : Matrix (Fin 2) (Fin 2) ℂ) :
    onSite (n := n) i A = tensorOpGen (fun k => if k = i then A else 1) := by
  ext x y
  unfold onSite tensorOpGen
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i)]
  have hrest : ∏ k ∈ Finset.univ.erase i, (if k = i then A else 1) (x k) (y k) =
      if ∀ j, j ≠ i → x j = y j then 1 else 0 := by
    by_cases hother : ∀ j, j ≠ i → x j = y j
    · rw [if_pos hother]
      refine Finset.prod_eq_one fun k hk => ?_
      have hki : k ≠ i := (Finset.mem_erase.mp hk).1
      simp [hki, hother k hki, Matrix.one_apply]
    · rw [if_neg hother]
      push Not at hother
      rcases hother with ⟨j, hji, hxy⟩
      exact Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨hji, Finset.mem_univ _⟩) (by simp [hji, hxy])
  simp [hrest]

private lemma onSite_mul_same {n : ℕ} (i : Fin n) (A B : Matrix (Fin 2) (Fin 2) ℂ) :
    onSite (n := n) i A * onSite (n := n) i B = onSite (n := n) i (A * B) := by
  rw [onSite_eq_tensorOpGen, onSite_eq_tensorOpGen, onSite_eq_tensorOpGen, tensorOpGen_mul]
  congr 1; ext k; split_ifs <;> simp

private lemma onSite_smul {n : ℕ} (i : Fin n) (c : ℂ) (A : Matrix (Fin 2) (Fin 2) ℂ) :
    onSite (n := n) i (c • A) = c • onSite (n := n) i A := by
  ext x y; simp [onSite, mul_assoc]

private lemma onSite_one {n : ℕ} (i : Fin n) : onSite (n := n) i 1 = 1 := by
  rw [onSite_eq_tensorOpGen]
  convert tensorOpGen_one (n := n) using 2
  ext k; split_ifs <;> rfl

private lemma onSite_comm {n : ℕ} {i j : Fin n} (hij : i ≠ j)
    (A B : Matrix (Fin 2) (Fin 2) ℂ) :
    onSite (n := n) i A * onSite (n := n) j B = onSite (n := n) j B * onSite (n := n) i A := by
  rw [onSite_eq_tensorOpGen, onSite_eq_tensorOpGen, tensorOpGen_mul, tensorOpGen_mul]
  congr 1; ext k
  by_cases hki : k = i
  · subst hki; simp [hij]
  · by_cases hkj : k = j
    · subst hkj; simp [hki]
    · simp [hki, hkj]

private lemma onSite_conjTranspose {n : ℕ} (i : Fin n) (A : Matrix (Fin 2) (Fin 2) ℂ) :
    (onSite (n := n) i A)ᴴ = onSite (n := n) i Aᴴ := by
  ext x y
  simp only [Matrix.conjTranspose_apply, onSite, star_mul']
  have heq : (if ∀ j, j ≠ i → y j = x j then (1 : ℂ) else 0) =
      if ∀ j, j ≠ i → x j = y j then 1 else 0 := by
    by_cases h : ∀ j, j ≠ i → x j = y j
    · rw [if_pos h, if_pos (fun j hj => (h j hj).symm)]
    · rw [if_neg h, if_neg (fun h' => h (fun j hj => (h' j hj).symm))]
  rw [show star (if ∀ j, j ≠ i → y j = x j then (1 : ℂ) else 0) =
      if ∀ j, j ≠ i → y j = x j then 1 else 0 by split_ifs <;> simp, heq, mul_comm]

private lemma dotSpin_comm {n : ℕ} {i j : Fin n} (hij : i ≠ j) :
    dotSpin i j = dotSpin j i := by
  unfold dotSpin
  rw [onSite_comm hij pauliX pauliX, onSite_comm hij pauliY pauliY, onSite_comm hij pauliZ pauliZ]

private lemma dotSpin_herm {n : ℕ} {i j : Fin n} (hij : i ≠ j) :
    (dotSpin i j)ᴴ = dotSpin i j := by
  unfold dotSpin
  simp only [Matrix.conjTranspose_add, Matrix.conjTranspose_mul, onSite_conjTranspose,
    pauliX_herm, pauliY_herm, pauliZ_herm]
  rw [onSite_comm hij.symm pauliX pauliX, onSite_comm hij.symm pauliY pauliY,
    onSite_comm hij.symm pauliZ pauliZ]

private lemma one_sub_dotSpin_sq {n : ℕ} {i j : Fin n} (hij : i ≠ j) :
    (1 - dotSpin i j) * (1 - dotSpin i j) = (4 : ℂ) • (1 - dotSpin i j) := by
  have hsq : dotSpin i j * dotSpin i j = (3 : ℂ) • 1 - (2 : ℂ) • dotSpin i j := by
    unfold dotSpin
    have hXX : (onSite i pauliX * onSite j pauliX) * (onSite i pauliX * onSite j pauliX) = 1 := by
      calc (onSite i pauliX * onSite j pauliX) * (onSite i pauliX * onSite j pauliX)
          = (onSite i pauliX * onSite i pauliX) * (onSite j pauliX * onSite j pauliX) := by
            rw [Matrix.mul_assoc, ← Matrix.mul_assoc (onSite j pauliX),
              onSite_comm hij.symm pauliX pauliX, Matrix.mul_assoc, ← Matrix.mul_assoc]
        _ = 1 := by rw [onSite_mul_same, onSite_mul_same, pauliX_sq, onSite_one, onSite_one, Matrix.one_mul]
    have hYY : (onSite i pauliY * onSite j pauliY) * (onSite i pauliY * onSite j pauliY) = 1 := by
      calc (onSite i pauliY * onSite j pauliY) * (onSite i pauliY * onSite j pauliY)
          = (onSite i pauliY * onSite i pauliY) * (onSite j pauliY * onSite j pauliY) := by
            rw [Matrix.mul_assoc, ← Matrix.mul_assoc (onSite j pauliY),
              onSite_comm hij.symm pauliY pauliY, Matrix.mul_assoc, ← Matrix.mul_assoc]
        _ = 1 := by rw [onSite_mul_same, onSite_mul_same, pauliY_sq, onSite_one, onSite_one, Matrix.one_mul]
    have hZZ : (onSite i pauliZ * onSite j pauliZ) * (onSite i pauliZ * onSite j pauliZ) = 1 := by
      calc (onSite i pauliZ * onSite j pauliZ) * (onSite i pauliZ * onSite j pauliZ)
          = (onSite i pauliZ * onSite i pauliZ) * (onSite j pauliZ * onSite j pauliZ) := by
            rw [Matrix.mul_assoc, ← Matrix.mul_assoc (onSite j pauliZ),
              onSite_comm hij.symm pauliZ pauliZ, Matrix.mul_assoc, ← Matrix.mul_assoc]
        _ = 1 := by rw [onSite_mul_same, onSite_mul_same, pauliZ_sq, onSite_one, onSite_one, Matrix.one_mul]
    have hXY : (onSite i pauliX * onSite j pauliX) * (onSite i pauliY * onSite j pauliY) =
        -(onSite i pauliZ * onSite j pauliZ) := by
      calc (onSite i pauliX * onSite j pauliX) * (onSite i pauliY * onSite j pauliY)
          = (onSite i pauliX * onSite i pauliY) * (onSite j pauliX * onSite j pauliY) := by
            rw [Matrix.mul_assoc, ← Matrix.mul_assoc (onSite j pauliX),
              onSite_comm hij.symm pauliX pauliY, Matrix.mul_assoc, ← Matrix.mul_assoc]
        _ = (Complex.I • onSite i pauliZ) * (Complex.I • onSite j pauliZ) := by
            rw [onSite_mul_same, onSite_mul_same, pauliX_mul_pauliY, onSite_smul, onSite_smul]
        _ = (Complex.I * Complex.I) • (onSite i pauliZ * onSite j pauliZ) := by
            rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
        _ = -(onSite i pauliZ * onSite j pauliZ) := by
            rw [Complex.I_mul_I, neg_one_smul]
    have hYX : (onSite i pauliY * onSite j pauliY) * (onSite i pauliX * onSite j pauliX) =
        -(onSite i pauliZ * onSite j pauliZ) := by
      calc (onSite i pauliY * onSite j pauliY) * (onSite i pauliX * onSite j pauliX)
          = (onSite i pauliY * onSite i pauliX) * (onSite j pauliY * onSite j pauliX) := by
            rw [Matrix.mul_assoc, ← Matrix.mul_assoc (onSite j pauliY),
              onSite_comm hij.symm pauliY pauliX, Matrix.mul_assoc, ← Matrix.mul_assoc]
        _ = ((-Complex.I) • onSite i pauliZ) * ((-Complex.I) • onSite j pauliZ) := by
            rw [onSite_mul_same, onSite_mul_same, pauliY_mul_pauliX, onSite_smul, onSite_smul]
        _ = ((-Complex.I) * (-Complex.I)) • (onSite i pauliZ * onSite j pauliZ) := by
            rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
        _ = -(onSite i pauliZ * onSite j pauliZ) := by
            simp [Complex.I_mul_I]
    have hYZ : (onSite i pauliY * onSite j pauliY) * (onSite i pauliZ * onSite j pauliZ) =
        -(onSite i pauliX * onSite j pauliX) := by
      calc (onSite i pauliY * onSite j pauliY) * (onSite i pauliZ * onSite j pauliZ)
          = (onSite i pauliY * onSite i pauliZ) * (onSite j pauliY * onSite j pauliZ) := by
            rw [Matrix.mul_assoc, ← Matrix.mul_assoc (onSite j pauliY),
              onSite_comm hij.symm pauliY pauliZ, Matrix.mul_assoc, ← Matrix.mul_assoc]
        _ = (Complex.I • onSite i pauliX) * (Complex.I • onSite j pauliX) := by
            rw [onSite_mul_same, onSite_mul_same, pauliY_mul_pauliZ, onSite_smul, onSite_smul]
        _ = -(onSite i pauliX * onSite j pauliX) := by
            rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Complex.I_mul_I, neg_one_smul]
    have hZY : (onSite i pauliZ * onSite j pauliZ) * (onSite i pauliY * onSite j pauliY) =
        -(onSite i pauliX * onSite j pauliX) := by
      calc (onSite i pauliZ * onSite j pauliZ) * (onSite i pauliY * onSite j pauliY)
          = (onSite i pauliZ * onSite i pauliY) * (onSite j pauliZ * onSite j pauliY) := by
            rw [Matrix.mul_assoc, ← Matrix.mul_assoc (onSite j pauliZ),
              onSite_comm hij.symm pauliZ pauliY, Matrix.mul_assoc, ← Matrix.mul_assoc]
        _ = ((-Complex.I) • onSite i pauliX) * ((-Complex.I) • onSite j pauliX) := by
            rw [onSite_mul_same, onSite_mul_same, pauliZ_mul_pauliY, onSite_smul, onSite_smul]
        _ = -(onSite i pauliX * onSite j pauliX) := by
            rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul]; simp [Complex.I_mul_I]
    have hZX : (onSite i pauliZ * onSite j pauliZ) * (onSite i pauliX * onSite j pauliX) =
        -(onSite i pauliY * onSite j pauliY) := by
      calc (onSite i pauliZ * onSite j pauliZ) * (onSite i pauliX * onSite j pauliX)
          = (onSite i pauliZ * onSite i pauliX) * (onSite j pauliZ * onSite j pauliX) := by
            rw [Matrix.mul_assoc, ← Matrix.mul_assoc (onSite j pauliZ),
              onSite_comm hij.symm pauliZ pauliX, Matrix.mul_assoc, ← Matrix.mul_assoc]
        _ = (Complex.I • onSite i pauliY) * (Complex.I • onSite j pauliY) := by
            rw [onSite_mul_same, onSite_mul_same, pauliZ_mul_pauliX, onSite_smul, onSite_smul]
        _ = -(onSite i pauliY * onSite j pauliY) := by
            rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Complex.I_mul_I, neg_one_smul]
    have hXZ : (onSite i pauliX * onSite j pauliX) * (onSite i pauliZ * onSite j pauliZ) =
        -(onSite i pauliY * onSite j pauliY) := by
      calc (onSite i pauliX * onSite j pauliX) * (onSite i pauliZ * onSite j pauliZ)
          = (onSite i pauliX * onSite i pauliZ) * (onSite j pauliX * onSite j pauliZ) := by
            rw [Matrix.mul_assoc, ← Matrix.mul_assoc (onSite j pauliX),
              onSite_comm hij.symm pauliX pauliZ, Matrix.mul_assoc, ← Matrix.mul_assoc]
        _ = ((-Complex.I) • onSite i pauliY) * ((-Complex.I) • onSite j pauliY) := by
            rw [onSite_mul_same, onSite_mul_same, pauliX_mul_pauliZ, onSite_smul, onSite_smul]
        _ = -(onSite i pauliY * onSite j pauliY) := by
            rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul]; simp [Complex.I_mul_I]
    simp only [Matrix.add_mul, Matrix.mul_add, hXX, hYY, hZZ, hXY, hYX, hYZ, hZY, hZX, hXZ]
    ext x y; simp; ring
  calc (1 - dotSpin i j) * (1 - dotSpin i j)
      = 1 - (2 : ℂ) • dotSpin i j + dotSpin i j * dotSpin i j := by
        simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one]
        ext x y; simp; ring
    _ = (4 : ℂ) • (1 - dotSpin i j) := by
        rw [hsq]; ext x y; simp; ring

private lemma energy_herm_sq_le {n : ℕ} (T : Op n) (hT : Tᴴ = T)
    (ψ : Config n → ℂ) (hψ : IsUnitState ψ) :
    (energy T ψ) ^ 2 ≤ energy (T * T) ψ := by
  have hnorm1 : ∑ x : Config n, ‖ψ x‖ ^ 2 = 1 := hψ
  have hnormT : ∑ x : Config n, ‖(T *ᵥ ψ) x‖ ^ 2 = energy (T * T) ψ := by
    have h1 : ∑ x : Config n, ‖(T *ᵥ ψ) x‖ ^ 2 = (star (T *ᵥ ψ) ⬝ᵥ (T *ᵥ ψ)).re := by
      simp only [dotProduct, Pi.star_apply, Complex.re_sum]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [Complex.star_def, mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.ofReal_re]
    rw [h1]
    unfold energy
    congr 1
    rw [Matrix.star_mulVec, hT, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec]
  have hcs : ‖star ψ ⬝ᵥ (T *ᵥ ψ)‖ ^ 2 ≤ (∑ x : Config n, ‖ψ x‖ ^ 2) * ∑ x : Config n, ‖(T *ᵥ ψ) x‖ ^ 2 := by
    calc ‖∑ x : Config n, star (ψ x) * (T *ᵥ ψ) x‖ ^ 2
        ≤ (∑ x : Config n, ‖star (ψ x) * (T *ᵥ ψ) x‖) ^ 2 := by
          gcongr; exact norm_sum_le _ _
      _ = (∑ x : Config n, ‖ψ x‖ * ‖(T *ᵥ ψ) x‖) ^ 2 := by
          congr 1; refine Finset.sum_congr rfl fun x _ => ?_; simp [norm_mul]
      _ ≤ (∑ x : Config n, ‖ψ x‖ ^ 2) * ∑ x : Config n, ‖(T *ᵥ ψ) x‖ ^ 2 :=
          Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun x => ‖ψ x‖) (fun x => ‖(T *ᵥ ψ) x‖)
  calc (energy T ψ) ^ 2
      = ((star ψ ⬝ᵥ (T *ᵥ ψ)).re) ^ 2 := rfl
    _ ≤ ‖star ψ ⬝ᵥ (T *ᵥ ψ)‖ ^ 2 := by
        calc ((star ψ ⬝ᵥ (T *ᵥ ψ)).re) ^ 2
            = |(star ψ ⬝ᵥ (T *ᵥ ψ)).re| ^ 2 := (sq_abs _).symm
          _ ≤ ‖star ψ ⬝ᵥ (T *ᵥ ψ)‖ ^ 2 := by gcongr; exact Complex.abs_re_le_norm _
    _ ≤ (∑ x : Config n, ‖ψ x‖ ^ 2) * ∑ x : Config n, ‖(T *ᵥ ψ) x‖ ^ 2 := hcs
    _ = energy (T * T) ψ := by rw [hnorm1, one_mul, hnormT]

private lemma energy_dotSpin_le_one {n : ℕ} {i j : Fin n} (hij : i ≠ j)
    (ψ : Config n → ℂ) (hψ : IsUnitState ψ) :
    energy (dotSpin i j) ψ ≤ 1 := by
  have h1 : 0 ≤ energy ((1 - dotSpin i j) * (1 - dotSpin i j)) ψ := by
    have hT : (1 - dotSpin i j)ᴴ = 1 - dotSpin i j := by
      simp [Matrix.conjTranspose_sub, dotSpin_herm hij]
    have hsq := energy_herm_sq_le (1 - dotSpin i j) hT ψ hψ
    linarith [sq_nonneg (energy (1 - dotSpin i j) ψ)]
  rw [one_sub_dotSpin_sq hij] at h1
  have he4 : energy ((4 : ℂ) • (1 - dotSpin i j)) ψ = 4 * (1 - energy (dotSpin i j) ψ) := by
    unfold energy
    have hnorm : (star ψ ⬝ᵥ ψ).re = 1 := by
      have : (star ψ ⬝ᵥ ψ).re = ∑ x : Config n, ‖ψ x‖ ^ 2 := by
        simp only [dotProduct, Pi.star_apply, Complex.re_sum]
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [Complex.star_def, mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.ofReal_re]
      rw [this]; exact hψ
    simp only [Matrix.smul_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec, dotProduct_smul,
      dotProduct_sub, smul_eq_mul, show (4 : ℂ) = ((4 : ℝ) : ℂ) by norm_num,
      Complex.re_ofReal_mul, Complex.sub_re, hnorm]
  linarith

private lemma energy_one {n : ℕ} (ψ : Config n → ℂ) (hψ : IsUnitState ψ) :
    energy (1 : Op n) ψ = 1 := by
  unfold energy
  rw [Matrix.one_mulVec]
  simp only [dotProduct, Pi.star_apply, Complex.re_sum]
  calc ∑ x : Config n, (star (ψ x) * ψ x).re
      = ∑ x : Config n, ‖ψ x‖ ^ 2 := by
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [Complex.star_def, mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.ofReal_re]
    _ = 1 := hψ

private lemma star_bound {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (w : Sym2 (Fin n) → ℝ) (hw : ∀ e, 0 ≤ w e) (v : Fin n)
    (ψ : Config n → ℂ) (hψ : IsUnitState ψ) :
    -energy (∑ u : Fin n, if G.Adj v u then ((w s(v, u) : ℝ) : ℂ) • dotSpin v u else 0) ψ ≤
      (∑ u : Fin n, if G.Adj v u then w s(v, u) else 0) + 2 * maxIncident G w v := by
  set S : Op n := ∑ u : Fin n, if G.Adj v u then ((w s(v, u) : ℝ) : ℂ) • dotSpin v u else 0
  set Wv : ℝ := ∑ u : Fin n, if G.Adj v u then w s(v, u) else 0
  set Mv : ℝ := maxIncident G w v
  have hWv_nonneg : 0 ≤ Wv := Finset.sum_nonneg fun u _ => by split_ifs <;> [exact hw _; exact le_rfl]
  have hMv_nonneg : 0 ≤ Mv := NNReal.coe_nonneg _
  have hle_Mv : ∀ u : Fin n, G.Adj v u → w s(v, u) ≤ Mv := by
    intro u hu
    have hmem : s(v, u) ∈ G.incidenceFinset v := by
      simp [SimpleGraph.mem_incidenceFinset, SimpleGraph.mem_incidenceSet, hu]
    have hsup : (w s(v, u)).toNNReal ≤ (G.incidenceFinset v).sup fun e => (w e).toNNReal :=
      Finset.le_sup (f := fun e => (w e).toNNReal) hmem
    have hcoe : ((w s(v, u)).toNNReal : ℝ) ≤ Mv := by exact_mod_cast hsup
    rwa [Real.coe_toNNReal _ (hw _)] at hcoe
  -- Define A σ = ∑ u, if G.Adj v u then w_{vu} • onSite u σ else 0
  let A : Matrix (Fin 2) (Fin 2) ℂ → Op n := fun σ =>
    ∑ u : Fin n, if G.Adj v u then ((w s(v, u) : ℝ) : ℂ) • onSite u σ else 0
  have hS_eq : S = onSite v pauliX * A pauliX + onSite v pauliY * A pauliY +
      onSite v pauliZ * A pauliZ := by
    simp only [S, A, Matrix.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun u _ => ?_
    split_ifs
    · simp only [Matrix.mul_smul, ← smul_add, dotSpin]
    · simp
  have hcomm_v : ∀ σ τ, onSite v σ * A τ = A τ * onSite v σ := by
    intro σ τ
    simp only [A, Matrix.mul_sum, Matrix.sum_mul]
    refine Finset.sum_congr rfl fun u _ => ?_
    split_ifs with hu
    · simp only [Matrix.mul_smul, Matrix.smul_mul, onSite_comm (G.ne_of_adj hu)]
    · simp
  have hsq_S : S * S = A pauliX * A pauliX + A pauliY * A pauliY + A pauliZ * A pauliZ -
      (2 : ℂ) • ∑ u : Fin n, if G.Adj v u then ((w s(v, u) ^ 2 : ℝ) : ℂ) • dotSpin v u else 0 := by
    rw [hS_eq]
    have hXX : (onSite v pauliX * A pauliX) * (onSite v pauliX * A pauliX) = A pauliX * A pauliX := by
      calc (onSite v pauliX * A pauliX) * (onSite v pauliX * A pauliX)
          = (onSite v pauliX * onSite v pauliX) * (A pauliX * A pauliX) := by
            rw [Matrix.mul_assoc, ← Matrix.mul_assoc (A pauliX), ← hcomm_v, Matrix.mul_assoc,
              ← Matrix.mul_assoc]
        _ = A pauliX * A pauliX := by rw [onSite_mul_same, pauliX_sq, onSite_one, Matrix.one_mul]
    have hYY : (onSite v pauliY * A pauliY) * (onSite v pauliY * A pauliY) = A pauliY * A pauliY := by
      calc (onSite v pauliY * A pauliY) * (onSite v pauliY * A pauliY)
          = (onSite v pauliY * onSite v pauliY) * (A pauliY * A pauliY) := by
            rw [Matrix.mul_assoc, ← Matrix.mul_assoc (A pauliY), ← hcomm_v, Matrix.mul_assoc,
              ← Matrix.mul_assoc]
        _ = A pauliY * A pauliY := by rw [onSite_mul_same, pauliY_sq, onSite_one, Matrix.one_mul]
    have hZZ : (onSite v pauliZ * A pauliZ) * (onSite v pauliZ * A pauliZ) = A pauliZ * A pauliZ := by
      calc (onSite v pauliZ * A pauliZ) * (onSite v pauliZ * A pauliZ)
          = (onSite v pauliZ * onSite v pauliZ) * (A pauliZ * A pauliZ) := by
            rw [Matrix.mul_assoc, ← Matrix.mul_assoc (A pauliZ), ← hcomm_v, Matrix.mul_assoc,
              ← Matrix.mul_assoc]
        _ = A pauliZ * A pauliZ := by rw [onSite_mul_same, pauliZ_sq, onSite_one, Matrix.one_mul]
    have hcross : ∀ σ τ ρ : Matrix (Fin 2) (Fin 2) ℂ,
        σ * τ = Complex.I • ρ → τ * σ = (-Complex.I) • ρ →
        (onSite v σ * A σ) * (onSite v τ * A τ) + (onSite v τ * A τ) * (onSite v σ * A σ) =
          -(2 : ℂ) • ∑ u : Fin n, if G.Adj v u then
            ((w s(v, u) ^ 2 : ℝ) : ℂ) • (onSite v ρ * onSite u ρ) else 0 := by
      intro σ τ ρ hst hts
      have h1 : (onSite v σ * A σ) * (onSite v τ * A τ) =
          Complex.I • (onSite v ρ * (A σ * A τ)) := by
        calc (onSite v σ * A σ) * (onSite v τ * A τ)
            = (onSite v σ * onSite v τ) * (A σ * A τ) := by
              rw [Matrix.mul_assoc, ← Matrix.mul_assoc (A σ), ← hcomm_v, Matrix.mul_assoc,
                ← Matrix.mul_assoc]
          _ = (Complex.I • onSite v ρ) * (A σ * A τ) := by
              rw [onSite_mul_same, hst, onSite_smul]
          _ = Complex.I • (onSite v ρ * (A σ * A τ)) := Matrix.smul_mul _ _ _
      have h2 : (onSite v τ * A τ) * (onSite v σ * A σ) =
          (-Complex.I) • (onSite v ρ * (A τ * A σ)) := by
        calc (onSite v τ * A τ) * (onSite v σ * A σ)
            = (onSite v τ * onSite v σ) * (A τ * A σ) := by
              rw [Matrix.mul_assoc, ← Matrix.mul_assoc (A τ), ← hcomm_v, Matrix.mul_assoc,
                ← Matrix.mul_assoc]
          _ = ((-Complex.I) • onSite v ρ) * (A τ * A σ) := by
              rw [onSite_mul_same, hts, onSite_smul]
          _ = (-Complex.I) • (onSite v ρ * (A τ * A σ)) := Matrix.smul_mul _ _ _
      have hcommA : A σ * A τ - A τ * A σ = (2 * Complex.I) • ∑ u : Fin n,
          if G.Adj v u then ((w s(v, u) ^ 2 : ℝ) : ℂ) • onSite u ρ else 0 := by
        simp only [A, Matrix.sum_mul, Matrix.mul_sum, Finset.smul_sum]
        rw [Finset.sum_comm (s := Finset.univ) (t := Finset.univ)
          (f := fun x a => (if G.Adj v a then ((w s(v, a) : ℝ) : ℂ) • onSite a σ else 0) *
            (if G.Adj v x then ((w s(v, x) : ℝ) : ℂ) • onSite x τ else 0))]
        rw [← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun u _ => ?_
        by_cases hu : G.Adj v u
        · rw [← Finset.sum_sub_distrib]
          rw [Finset.sum_eq_single u]
          · simp only [hu, ↓reduceIte, Matrix.smul_mul, Matrix.mul_smul, smul_smul, ← smul_sub,
              onSite_mul_same, hst, hts, onSite_smul]
            ext x y; simp; ring
          · intro u' _ hu'
            by_cases hu'v : G.Adj v u'
            · simp only [hu, hu'v, ↓reduceIte, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
              rw [onSite_comm hu'.symm, mul_comm ((w s(v, u') : ℝ) : ℂ), sub_self]
            · simp [hu'v]
          · intro hu_mem; exact absurd (Finset.mem_univ _) hu_mem
        · simp [hu]
      calc (onSite v σ * A σ) * (onSite v τ * A τ) + (onSite v τ * A τ) * (onSite v σ * A σ)
          = Complex.I • (onSite v ρ * (A σ * A τ - A τ * A σ)) := by
            rw [h1, h2]
            ext x y; simp [Matrix.mul_sub]; ring
        _ = Complex.I • (onSite v ρ * ((2 * Complex.I) • ∑ u : Fin n,
              if G.Adj v u then ((w s(v, u) ^ 2 : ℝ) : ℂ) • onSite u ρ else 0)) := by rw [hcommA]
        _ = -(2 : ℂ) • ∑ u : Fin n, if G.Adj v u then
              ((w s(v, u) ^ 2 : ℝ) : ℂ) • (onSite v ρ * onSite u ρ) else 0 := by
            rw [Matrix.mul_smul, smul_smul, Matrix.mul_sum]
            have hI2 : Complex.I * (2 * Complex.I) = -2 := by
              calc Complex.I * (2 * Complex.I) = 2 * (Complex.I * Complex.I) := by ring
                _ = -2 := by rw [Complex.I_mul_I]; ring
            rw [hI2, neg_smul]
            ext x y
            simp only [Matrix.neg_apply, Matrix.smul_apply, Matrix.sum_apply, smul_eq_mul, nsmul_eq_mul]
            simp_rw [Finset.mul_sum]
            rw [← Finset.sum_neg_distrib]
            refine Finset.sum_congr rfl fun u _ => ?_
            by_cases hu : G.Adj v u <;> simp [hu]
    have hXY := hcross pauliX pauliY pauliZ pauliX_mul_pauliY pauliY_mul_pauliX
    have hYZ := hcross pauliY pauliZ pauliX pauliY_mul_pauliZ pauliZ_mul_pauliY
    have hZX := hcross pauliZ pauliX pauliY pauliZ_mul_pauliX pauliX_mul_pauliZ
    simp only [Matrix.add_mul, Matrix.mul_add]
    calc _ = (onSite v pauliX * A pauliX) * (onSite v pauliX * A pauliX) +
             (onSite v pauliY * A pauliY) * (onSite v pauliY * A pauliY) +
             (onSite v pauliZ * A pauliZ) * (onSite v pauliZ * A pauliZ) +
             ((onSite v pauliX * A pauliX) * (onSite v pauliY * A pauliY) +
              (onSite v pauliY * A pauliY) * (onSite v pauliX * A pauliX)) +
             ((onSite v pauliY * A pauliY) * (onSite v pauliZ * A pauliZ) +
              (onSite v pauliZ * A pauliZ) * (onSite v pauliY * A pauliY)) +
             ((onSite v pauliZ * A pauliZ) * (onSite v pauliX * A pauliX) +
              (onSite v pauliX * A pauliX) * (onSite v pauliZ * A pauliZ)) := by abel
      _ = A pauliX * A pauliX + A pauliY * A pauliY + A pauliZ * A pauliZ -
            (2 : ℂ) • ∑ u : Fin n, if G.Adj v u then ((w s(v, u) ^ 2 : ℝ) : ℂ) • dotSpin v u else 0 := by
          rw [hXX, hYY, hZZ, hXY, hYZ, hZX]
          ext x y
          simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.sum_apply,
            smul_eq_mul]
          have hsum3 : (∑ u : Fin n, (if G.Adj v u then ((w s(v, u) ^ 2 : ℝ) : ℂ) •
              (onSite v pauliZ * onSite u pauliZ) else 0) x y) +
              (∑ u : Fin n, (if G.Adj v u then ((w s(v, u) ^ 2 : ℝ) : ℂ) •
              (onSite v pauliX * onSite u pauliX) else 0) x y) +
              (∑ u : Fin n, (if G.Adj v u then ((w s(v, u) ^ 2 : ℝ) : ℂ) •
              (onSite v pauliY * onSite u pauliY) else 0) x y) =
              ∑ u : Fin n, (if G.Adj v u then ((w s(v, u) ^ 2 : ℝ) : ℂ) •
                dotSpin v u else 0) x y := by
            simp only [← Finset.sum_add_distrib]
            refine Finset.sum_congr rfl fun u _ => ?_
            by_cases hu : G.Adj v u
            · simp only [hu, ↓reduceIte, Matrix.smul_apply, smul_eq_mul, dotSpin, Matrix.add_apply]
              ring
            · simp [hu]
          linear_combination -2 * hsum3
  -- Now bound energy ((S + Mv • 1) * (S + Mv • 1)) ψ ≤ (Wv + Mv)^2
  set T : Op n := S + ((Mv : ℝ) : ℂ) • (1 : Op n)
  have hS_herm : Sᴴ = S := by
    simp only [S, Matrix.conjTranspose_sum]
    refine Finset.sum_congr rfl fun u _ => ?_
    split_ifs with hu
    · simp [Matrix.conjTranspose_smul, Complex.conj_ofReal, dotSpin_herm (G.ne_of_adj hu)]
    · simp
  have hT_herm : Tᴴ = T := by
    simp only [T, Matrix.conjTranspose_add, hS_herm, Matrix.conjTranspose_smul,
      Complex.star_def, Complex.conj_ofReal, Matrix.conjTranspose_one]
  have hT_sq_energy : energy (T * T) ψ ≤ (Wv + Mv) ^ 2 := by
    have hTT : T * T = A pauliX * A pauliX + A pauliY * A pauliY + A pauliZ * A pauliZ +
        ((2 : ℂ) • ∑ u : Fin n, if G.Adj v u then
          ((w s(v, u) * (Mv - w s(v, u)) : ℝ) : ℂ) • dotSpin v u else 0) +
        ((Mv ^ 2 : ℝ) : ℂ) • (1 : Op n) := by
      calc T * T = S * S + ((2 * Mv : ℝ) : ℂ) • S + ((Mv ^ 2 : ℝ) : ℂ) • (1 : Op n) := by
            simp only [T, Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul,
              Matrix.one_mul, Matrix.mul_one, smul_smul]
            ext x y; simp; ring
        _ = _ := by
            rw [hsq_S]
            have h2diff : ((2 * Mv : ℝ) : ℂ) • S - (2 : ℂ) • ∑ u : Fin n,
                (if G.Adj v u then ((w s(v, u) ^ 2 : ℝ) : ℂ) • dotSpin v u else 0) =
                (2 : ℂ) • ∑ u : Fin n, if G.Adj v u then
                  ((w s(v, u) * (Mv - w s(v, u)) : ℝ) : ℂ) • dotSpin v u else 0 := by
              simp only [S, Finset.smul_sum, ← Finset.sum_sub_distrib]
              refine Finset.sum_congr rfl fun u _ => ?_
              split_ifs
              · ext x y; simp; ring
              · simp
            ext x y
            have h2diff_xy := congr_fun (congr_fun h2diff x) y
            simp only [Matrix.add_apply, Matrix.sub_apply] at h2diff_xy ⊢
            linear_combination h2diff_xy
    -- Bound energy of A_X^2 + A_Y^2 + A_Z^2
    have hAAA : A pauliX * A pauliX + A pauliY * A pauliY + A pauliZ * A pauliZ =
        ((3 * ∑ u : Fin n, if G.Adj v u then w s(v, u) ^ 2 else 0 : ℝ) : ℂ) • (1 : Op n) +
        ∑ u : Fin n, ∑ u' : Fin n, if G.Adj v u ∧ G.Adj v u' ∧ u ≠ u' then
          ((w s(v, u) * w s(v, u') : ℝ) : ℂ) • dotSpin u u' else 0 := by
      have hA_sq : ∀ σ : Matrix (Fin 2) (Fin 2) ℂ, σ * σ = 1 →
          A σ * A σ = ((∑ u : Fin n, if G.Adj v u then w s(v, u) ^ 2 else 0 : ℝ) : ℂ) • (1 : Op n) +
            ∑ u : Fin n, ∑ u' : Fin n, if G.Adj v u ∧ G.Adj v u' ∧ u ≠ u' then
              ((w s(v, u) * w s(v, u') : ℝ) : ℂ) • (onSite u σ * onSite u' σ) else 0 := by
        intro σ hσ
        simp only [A, Matrix.sum_mul, Matrix.mul_sum]
        rw [Finset.sum_comm]
        have hdiag_off : ∀ u : Fin n, (∑ u' : Fin n,
            (if G.Adj v u then ((w s(v, u) : ℝ) : ℂ) • onSite u σ else 0) *
            (if G.Adj v u' then ((w s(v, u') : ℝ) : ℂ) • onSite u' σ else 0)) =
            (if G.Adj v u then ((w s(v, u) ^ 2 : ℝ) : ℂ) • (1 : Op n) else 0) +
            ∑ u' : Fin n, if G.Adj v u ∧ G.Adj v u' ∧ u ≠ u' then
              ((w s(v, u) * w s(v, u') : ℝ) : ℂ) • (onSite u σ * onSite u' σ) else 0 := by
          intro u
          rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ u)]
          congr 1
          · by_cases hu : G.Adj v u
            · rw [if_pos hu, if_pos hu, Matrix.smul_mul, Matrix.mul_smul, smul_smul, onSite_mul_same, hσ,
                onSite_one]
              congr 1; push_cast; ring
            · simp [hu]
          · rw [← Finset.sum_erase_add _ _ (Finset.mem_univ u)]
            have hzero_u : (if G.Adj v u ∧ G.Adj v u ∧ u ≠ u then
                ((w s(v, u) * w s(v, u) : ℝ) : ℂ) • (onSite u σ * onSite u σ) else 0) = 0 :=
              if_neg (fun h => h.2.2 rfl)
            rw [hzero_u, add_zero]
            refine Finset.sum_congr rfl fun u' hu' => ?_
            have hne : u ≠ u' := (Finset.mem_erase.mp hu').1.symm
            by_cases hu : G.Adj v u <;> by_cases hu'adj : G.Adj v u'
            · rw [if_pos hu, if_pos hu'adj, if_pos ⟨hu, hu'adj, hne⟩,
                Matrix.smul_mul, Matrix.mul_smul, smul_smul]; push_cast; rfl
            · simp only [hu, hu'adj, ↓reduceIte, false_and, and_false, zero_mul, mul_zero]
            · simp only [hu, hu'adj, ↓reduceIte, false_and, and_false, zero_mul, mul_zero]
            · simp only [hu, hu'adj, ↓reduceIte, false_and, and_false, zero_mul, mul_zero]
        simp_rw [hdiag_off, Finset.sum_add_distrib]
        congr 1
        ext x y
        simp only [Matrix.sum_apply, Matrix.ite_apply, Matrix.zero_apply, Matrix.smul_apply,
          smul_eq_mul]
        push_cast
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun c _ => ?_
        split_ifs <;> simp
      rw [hA_sq pauliX pauliX_sq, hA_sq pauliY pauliY_sq, hA_sq pauliZ pauliZ_sq]
      simp only [add_assoc]
      have h1_sum : ((∑ u : Fin n, if G.Adj v u then w s(v, u) ^ 2 else 0 : ℝ) : ℂ) • (1 : Op n) +
          (((∑ u : Fin n, if G.Adj v u then w s(v, u) ^ 2 else 0 : ℝ) : ℂ) • (1 : Op n) +
          ((∑ u : Fin n, if G.Adj v u then w s(v, u) ^ 2 else 0 : ℝ) : ℂ) • (1 : Op n)) =
          ((3 * ∑ u : Fin n, if G.Adj v u then w s(v, u) ^ 2 else 0 : ℝ) : ℂ) • (1 : Op n) := by
        rw [← add_smul, ← add_smul]; congr 1; push_cast; ring
      have hdot_sum : (∑ u : Fin n, ∑ u' : Fin n,
          if G.Adj v u ∧ G.Adj v u' ∧ u ≠ u' then
            ((w s(v, u) * w s(v, u') : ℝ) : ℂ) • (onSite u pauliX * onSite u' pauliX) else 0) +
          ((∑ u : Fin n, ∑ u' : Fin n,
          if G.Adj v u ∧ G.Adj v u' ∧ u ≠ u' then
            ((w s(v, u) * w s(v, u') : ℝ) : ℂ) • (onSite u pauliY * onSite u' pauliY) else 0) +
          (∑ u : Fin n, ∑ u' : Fin n,
          if G.Adj v u ∧ G.Adj v u' ∧ u ≠ u' then
            ((w s(v, u) * w s(v, u') : ℝ) : ℂ) • (onSite u pauliZ * onSite u' pauliZ) else 0)) =
          ∑ u : Fin n, ∑ u' : Fin n, if G.Adj v u ∧ G.Adj v u' ∧ u ≠ u' then
            ((w s(v, u) * w s(v, u') : ℝ) : ℂ) • dotSpin u u' else 0 := by
        simp only [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun u' _ => ?_
        split_ifs
        · simp only [← smul_add, dotSpin]; abel
        · simp
      ext x y
      have h1_xy := congr_fun (congr_fun h1_sum x) y
      have hdot_xy := congr_fun (congr_fun hdot_sum x) y
      simp only [Matrix.add_apply] at h1_xy hdot_xy ⊢
      linear_combination h1_xy + hdot_xy
    have he_add : ∀ A B : Op n, energy (A + B) ψ = energy A ψ + energy B ψ := by
      intro A B; unfold energy; simp [Matrix.add_mulVec, dotProduct_add, Complex.add_re]
    have he_smul : ∀ (r : ℝ) (A : Op n), energy ((r : ℂ) • A) ψ = r * energy A ψ := by
      intro r A; unfold energy; simp [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul, Complex.re_ofReal_mul]
    have he_sum : ∀ (s : Finset (Fin n)) (f : Fin n → Op n),
        energy (∑ a ∈ s, f a) ψ = ∑ a ∈ s, energy (f a) ψ := by
      intro s f
      induction s using Finset.induction_on with
      | empty => unfold energy; simp
      | @insert a s ha ih => rw [Finset.sum_insert ha, he_add, ih, Finset.sum_insert ha]
    have hsum_sq_eq : (∑ u : Fin n, ∑ u' : Fin n,
        if G.Adj v u ∧ G.Adj v u' ∧ u ≠ u' then w s(v, u) * w s(v, u') else 0) =
        Wv ^ 2 - ∑ u : Fin n, if G.Adj v u then w s(v, u) ^ 2 else 0 := by
      have hW2 : Wv ^ 2 = ∑ u : Fin n, ∑ u' : Fin n,
          (if G.Adj v u then w s(v, u) else 0) * (if G.Adj v u' then w s(v, u') else 0) := by
        simp only [Wv, sq, Finset.sum_mul, Finset.mul_sum]; rw [Finset.sum_comm]
      rw [hW2]
      have hsplit : ∀ u : Fin n, (∑ u' : Fin n,
          (if G.Adj v u then w s(v, u) else 0) * (if G.Adj v u' then w s(v, u') else 0)) =
          (if G.Adj v u then w s(v, u) ^ 2 else 0) +
          ∑ u' : Fin n, if G.Adj v u ∧ G.Adj v u' ∧ u ≠ u' then w s(v, u) * w s(v, u') else 0 := by
        intro u
        rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ u)]
        congr 1
        · split_ifs <;> ring
        · rw [← Finset.sum_erase_add _ _ (Finset.mem_univ u)]
          simp only [ne_eq, not_true_eq_false, and_false, ↓reduceIte, add_zero]
          refine Finset.sum_congr rfl fun u' hu' => ?_
          have hne : u ≠ u' := (Finset.mem_erase.mp hu').1.symm
          split_ifs with h1 h2 h3 <;> simp_all
      simp_rw [hsplit, Finset.sum_add_distrib]
      ring
    have he_2 : (2 : ℂ) = ((2 : ℝ) : ℂ) := by norm_num
    rw [hTT, hAAA, he_2]
    simp only [he_add, he_smul, he_sum, energy_one ψ hψ, mul_one]
    have hbound1 : ∑ x : Fin n, ∑ x_1 : Fin n, energy
        (if G.Adj v x ∧ G.Adj v x_1 ∧ x ≠ x_1 then
          ((w s(v, x) * w s(v, x_1) : ℝ) : ℂ) • dotSpin x x_1 else 0) ψ ≤
        ∑ x : Fin n, ∑ x_1 : Fin n,
          if G.Adj v x ∧ G.Adj v x_1 ∧ x ≠ x_1 then w s(v, x) * w s(v, x_1) else 0 := by
      refine Finset.sum_le_sum fun u _ => Finset.sum_le_sum fun u' _ => ?_
      split_ifs with h
      · rw [he_smul]
        exact mul_le_of_le_one_right (mul_nonneg (hw _) (hw _)) (energy_dotSpin_le_one h.2.2 ψ hψ)
      · unfold energy; simp
    have hbound2 : ∑ x : Fin n, energy (if G.Adj v x then
        ((w s(v, x) * (Mv - w s(v, x)) : ℝ) : ℂ) • dotSpin v x else 0) ψ ≤
        ∑ x : Fin n, if G.Adj v x then w s(v, x) * (Mv - w s(v, x)) else 0 := by
      refine Finset.sum_le_sum fun u _ => ?_
      split_ifs with hu
      · rw [he_smul]
        have hnn : 0 ≤ w s(v, u) * (Mv - w s(v, u)) := mul_nonneg (hw _) (sub_nonneg.mpr (hle_Mv u hu))
        exact mul_le_of_le_one_right hnn (energy_dotSpin_le_one (G.ne_of_adj hu) ψ hψ)
      · unfold energy; simp
    have h2_eq : (2 : ℝ) * ∑ u : Fin n, (if G.Adj v u then w s(v, u) * (Mv - w s(v, u)) else 0) =
        2 * Mv * Wv - 2 * ∑ u : Fin n, if G.Adj v u then w s(v, u) ^ 2 else 0 := by
      have hsub : ∀ u : Fin n, (if G.Adj v u then w s(v, u) * (Mv - w s(v, u)) else 0) =
          Mv * (if G.Adj v u then w s(v, u) else 0) - (if G.Adj v u then w s(v, u) ^ 2 else 0) := by
        intro u; split_ifs <;> ring
      simp_rw [hsub, Finset.sum_sub_distrib, ← Finset.mul_sum]
      change 2 * (Mv * Wv - ∑ u : Fin n, if G.Adj v u then w s(v, u) ^ 2 else 0) = _
      ring
    have he_2 : (2 : ℂ) = ((2 : ℝ) : ℂ) := by norm_num
    rw [he_2] at *
    linarith [hbound1, hbound2, hsum_sq_eq, h2_eq]
  have hsq_le := energy_herm_sq_le T hT_herm ψ hψ
  have he_T : energy T ψ = energy S ψ + Mv := by
    unfold energy
    simp only [T, Matrix.add_mulVec, Matrix.smul_mulVec, dotProduct_add, dotProduct_smul,
      Complex.add_re, smul_eq_mul, Complex.re_ofReal_mul]
    have h1 := energy_one ψ hψ
    unfold energy at h1
    rw [h1, mul_one]
  have hle : -(Wv + Mv) ≤ energy S ψ + Mv := by
    have hsq2 : (energy S ψ + Mv) ^ 2 ≤ (Wv + Mv) ^ 2 := by
      rw [← he_T]; exact le_trans hsq_le hT_sq_energy
    nlinarith [add_nonneg hWv_nonneg hMv_nonneg]
  linarith

private lemma totalWeight_eq_sum_lt {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (w : Sym2 (Fin n) → ℝ) :
    totalWeight G w = ∑ i : Fin n, ∑ j : Fin n, if i < j ∧ G.Adj i j then w s(i, j) else 0 := by
  unfold totalWeight
  have hR : (∑ i : Fin n, ∑ j : Fin n, if i < j ∧ G.Adj i j then w s(i, j) else 0) =
      ∑ p ∈ Finset.univ.filter (fun p : Fin n × Fin n => p.1 < p.2 ∧ G.Adj p.1 p.2), w s(p.1, p.2) := by
    rw [Finset.sum_filter, Fintype.sum_prod_type]
  rw [hR]
  refine (Finset.sum_bij (fun p _ => s(p.1, p.2)) ?_ ?_ ?_ ?_).symm
  · intro p hp
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
    exact G.mem_edgeFinset.mpr hp.2
  · intro p hp q hq h
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp hq
    rw [Sym2.eq_iff] at h
    rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Prod.ext h1 h2
    · exfalso; exact absurd (h1 ▸ hp.1) (not_lt.mpr (le_of_lt (h2 ▸ hq.1)))
  · intro e he
    rw [G.mem_edgeFinset] at he
    induction e using Sym2.ind with
    | _ a b =>
      have hab : a ≠ b := G.ne_of_adj he
      rcases lt_or_gt_of_ne hab with h | h
      · exact ⟨(a, b), Finset.mem_filter.mpr ⟨Finset.mem_univ _, h, he⟩, rfl⟩
      · exact ⟨(b, a), Finset.mem_filter.mpr ⟨Finset.mem_univ _, h, he.symm⟩, Sym2.eq_swap⟩
  · intro _ _; rfl

private theorem weighted_eq_15_aux {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (w : Sym2 (Fin n) → ℝ) (hw : ∀ e, 0 ≤ w e)
    (ψ : Config n → ℂ) (hψ : IsUnitState ψ) :
    energy (hamiltonian G w) ψ ≤ totalWeight G w + (1 / 2) * ∑ v, maxIncident G w v := by
  have he_add : ∀ A B : Op n, energy (A + B) ψ = energy A ψ + energy B ψ := by
    intro A B; unfold energy; simp [Matrix.add_mulVec, dotProduct_add, Complex.add_re]
  have he_sub : ∀ A B : Op n, energy (A - B) ψ = energy A ψ - energy B ψ := by
    intro A B; unfold energy; simp [Matrix.sub_mulVec, dotProduct_sub, Complex.sub_re]
  have he_smul : ∀ (r : ℝ) (A : Op n), energy ((r : ℂ) • A) ψ = r * energy A ψ := by
    intro r A; unfold energy; simp [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul, Complex.re_ofReal_mul]
  have he_sum : ∀ (s : Finset (Fin n)) (f : Fin n → Op n),
      energy (∑ a ∈ s, f a) ψ = ∑ a ∈ s, energy (f a) ψ := by
    intro s f
    induction s using Finset.induction_on with
    | empty => unfold energy; simp
    | @insert a s ha ih => rw [Finset.sum_insert ha, he_add, ih, Finset.sum_insert ha]
  have hham_decomp : hamiltonian G w = ((totalWeight G w / 2 : ℝ) : ℂ) • (1 : Op n) -
      ((1 / 4 : ℝ) : ℂ) • ∑ v : Fin n, ∑ u : Fin n,
        if G.Adj v u then ((w s(v, u) : ℝ) : ℂ) • dotSpin v u else 0 := by
    have hedge : ∀ i j : Fin n, edgeTerm i j = ((1 / 2 : ℝ) : ℂ) • (1 - dotSpin i j) := by
      intro i j; unfold edgeTerm dotSpin; push_cast; simp [sub_sub]
    have h1 : hamiltonian G w = ((totalWeight G w / 2 : ℝ) : ℂ) • (1 : Op n) -
        ((1 / 2 : ℝ) : ℂ) • ∑ i : Fin n, ∑ j : Fin n,
          if i < j ∧ G.Adj i j then ((w s(i, j) : ℝ) : ℂ) • dotSpin i j else 0 := by
      unfold hamiltonian
      simp_rw [hedge]
      have hsplit : ∀ i j : Fin n,
          (if i < j ∧ G.Adj i j then ((w s(i, j) : ℝ) : ℂ) • ((1 / 2 : ℝ) : ℂ) • (1 - dotSpin i j) else 0) =
          (if i < j ∧ G.Adj i j then ((w s(i, j) / 2 : ℝ) : ℂ) • (1 : Op n) else 0) -
          (if i < j ∧ G.Adj i j then ((1 / 2 : ℝ) : ℂ) • ((w s(i, j) : ℝ) : ℂ) • dotSpin i j else 0) := by
        intro i j; split_ifs
        · simp only [smul_sub, smul_smul]
          congr 1 <;> congr 1 <;> push_cast <;> ring
        · simp
      simp_rw [hsplit, Finset.sum_sub_distrib]
      congr 1
      · rw [totalWeight_eq_sum_lt G w]
        simp only [Finset.sum_div]
        push_cast
        simp_rw [Finset.sum_smul]
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
        split_ifs <;> simp
      · simp only [Finset.smul_sum]
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
        split_ifs <;> simp
    have h2 : ∑ v : Fin n, ∑ u : Fin n,
        (if G.Adj v u then ((w s(v, u) : ℝ) : ℂ) • dotSpin v u else 0) =
        (2 : ℂ) • ∑ i : Fin n, ∑ j : Fin n,
          if i < j ∧ G.Adj i j then ((w s(i, j) : ℝ) : ℂ) • dotSpin i j else 0 := by
      have hsymm : ∀ v u : Fin n,
          (if G.Adj v u then ((w s(v, u) : ℝ) : ℂ) • dotSpin v u else 0) =
          (if v < u ∧ G.Adj v u then ((w s(v, u) : ℝ) : ℂ) • dotSpin v u else 0) +
          (if u < v ∧ G.Adj u v then ((w s(u, v) : ℝ) : ℂ) • dotSpin u v else 0) := by
        intro v u
        by_cases h : G.Adj v u
        · have hne : v ≠ u := G.ne_of_adj h
          rcases lt_or_gt_of_ne hne with hlt | hgt
          · rw [if_pos h, if_pos ⟨hlt, h⟩, if_neg (fun h' => lt_asymm hlt h'.1), add_zero]
          · rw [if_pos h, if_neg (fun h' => lt_asymm hgt h'.1), if_pos ⟨hgt, h.symm⟩, zero_add,
              Sym2.eq_swap, dotSpin_comm hne]
        · rw [if_neg h, if_neg (fun h' => h h'.2), if_neg (fun h' => h h'.2.symm), add_zero]
      simp_rw [hsymm, Finset.sum_add_distrib]
      have hswap : (∑ v : Fin n, ∑ u : Fin n,
          if u < v ∧ G.Adj u v then ((w s(u, v) : ℝ) : ℂ) • dotSpin u v else 0) =
          ∑ i : Fin n, ∑ j : Fin n,
          if i < j ∧ G.Adj i j then ((w s(i, j) : ℝ) : ℂ) • dotSpin i j else 0 :=
        Finset.sum_comm
      rw [hswap, ← two_smul ℂ]
    rw [h1, h2, smul_smul]
    norm_num
  have hW_sum : ∑ v : Fin n, (∑ u : Fin n, if G.Adj v u then w s(v, u) else 0) = 2 * totalWeight G w := by
    have hsymm : ∀ v u : Fin n,
        (if G.Adj v u then w s(v, u) else 0) =
        (if v < u ∧ G.Adj v u then w s(v, u) else 0) +
        (if u < v ∧ G.Adj u v then w s(u, v) else 0) := by
      intro v u
      by_cases h : G.Adj v u
      · rcases lt_or_gt_of_ne (G.ne_of_adj h) with hlt | hgt
        · rw [if_pos h, if_pos ⟨hlt, h⟩, if_neg (fun h' => lt_asymm hlt h'.1), add_zero]
        · rw [if_pos h, if_neg (fun h' => lt_asymm hgt h'.1), if_pos ⟨hgt, h.symm⟩, zero_add,
            Sym2.eq_swap]
      · rw [if_neg h, if_neg (fun h' => h h'.2), if_neg (fun h' => h h'.2.symm), add_zero]
    simp_rw [hsymm, Finset.sum_add_distrib]
    rw [Finset.sum_comm (s := Finset.univ) (t := Finset.univ)
      (f := fun v u => if u < v ∧ G.Adj u v then w s(u, v) else 0),
      ← totalWeight_eq_sum_lt G w]
    ring
  rw [hham_decomp]
  simp only [he_sub, he_smul, he_sum, energy_one ψ hψ, mul_one]
  have hstar : -∑ v : Fin n, energy (∑ u : Fin n, if G.Adj v u then ((w s(v, u) : ℝ) : ℂ) • dotSpin v u else 0) ψ ≤
      ∑ v : Fin n, ((∑ u : Fin n, if G.Adj v u then w s(v, u) else 0) + 2 * maxIncident G w v) := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_le_sum fun v _ => star_bound G w hw v ψ hψ
  rw [Finset.sum_add_distrib, hW_sum, ← Finset.mul_sum] at hstar
  simp_rw [he_sum] at hstar
  linarith

end QMaxCutBeyond.TwoQubit

open QMaxCutBeyond.TwoQubit

theorem solution {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (w : Sym2 (Fin n) → ℝ) (hw : ∀ e, 0 ≤ w e)
    (ψ : Config n → ℂ) (hψ : IsUnitState ψ) :
    energy (hamiltonian G w) ψ ≤ totalWeight G w + (1 / 2) * ∑ v, maxIncident G w v :=
  weighted_eq_15_aux G w hw ψ hψ