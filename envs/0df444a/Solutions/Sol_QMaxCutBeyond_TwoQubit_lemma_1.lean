-- Prove2me | solution 1 for QMaxCutBeyond.TwoQubit.lemma_1
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-19T03:55:25.228475+00:00
-- url     : https://prove2.me/submissions/06fa9812-01af-4ff0-ab15-a69368a58522

import Mathlib
import Definitions.Def_QMaxCutBeyond_TwoQubit_Setting

open Matrix QMaxCutBeyond.TwoQubit

private lemma pauliX_sq : pauliX * pauliX = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [pauliX, Matrix.mul_apply]

private lemma pauliY_sq : pauliY * pauliY = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [pauliY, Matrix.mul_apply, Complex.I_sq]

private lemma pauliZ_sq : pauliZ * pauliZ = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [pauliZ, Matrix.mul_apply]

private lemma pauliX_herm : pauliX.IsHermitian := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [pauliX]

private lemma pauliY_herm : pauliY.IsHermitian := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [pauliY]

private lemma pauliZ_herm : pauliZ.IsHermitian := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [pauliZ]

private lemma pauliXY_anti : pauliX * pauliY + pauliY * pauliX = 0 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [pauliX, pauliY, Matrix.mul_apply]

private lemma pauliXZ_anti : pauliX * pauliZ + pauliZ * pauliX = 0 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [pauliX, pauliZ, Matrix.mul_apply]

private lemma pauliYZ_anti : pauliY * pauliZ + pauliZ * pauliY = 0 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [pauliY, pauliZ, Matrix.mul_apply]

private lemma onSite_herm {n : ℕ} (i : Fin n) (σ : Matrix (Fin 2) (Fin 2) ℂ)
    (hσ : σ.IsHermitian) : (onSite i σ).IsHermitian := by
  ext x y
  simp only [Matrix.conjTranspose_apply, onSite, star_mul']
  have hcond : (∀ j, j ≠ i → y j = x j) ↔ (∀ j, j ≠ i → x j = y j) :=
    forall₂_congr fun _ _ => eq_comm
  have hstar : star (σ (y i) (x i)) = σ (x i) (y i) := by
    have := congr_fun (congr_fun hσ (x i)) (y i)
    simpa [Matrix.conjTranspose_apply] using this
  by_cases h1 : ∀ j, j ≠ i → y j = x j
  · rw [if_pos h1, if_pos (hcond.mp h1), hstar]
    simp
  · rw [if_neg h1, if_neg (fun h2 => h1 (hcond.mpr h2))]
    simp

private lemma onSite_mul_same {n : ℕ} (i : Fin n) (σ τ : Matrix (Fin 2) (Fin 2) ℂ) :
    onSite i σ * onSite i τ = onSite i (σ * τ) := by
  ext x y
  simp only [Matrix.mul_apply, onSite]
  by_cases h : ∀ j, j ≠ i → x j = y j
  · simp only [if_pos h, mul_one]
    let f : Fin 2 → Config n := fun b j => if j = i then b else x j
    have hsum : (∑ z : Config n,
        (σ (x i) (z i) * if ∀ j, j ≠ i → x j = z j then (1 : ℂ) else 0) *
          (τ (z i) (y i) * if ∀ j, j ≠ i → z j = y j then (1 : ℂ) else 0)) =
        ∑ b : Fin 2, σ (x i) b * τ b (y i) := by
      have hother : ∀ z : Config n, z ∉ Finset.image f Finset.univ →
          (σ (x i) (z i) * if ∀ j, j ≠ i → x j = z j then (1 : ℂ) else 0) *
            (τ (z i) (y i) * if ∀ j, j ≠ i → z j = y j then (1 : ℂ) else 0) = 0 := by
        intro z hz
        by_cases hz1 : ∀ j, j ≠ i → x j = z j
        · exfalso; apply hz
          rw [Finset.mem_image]
          refine ⟨z i, Finset.mem_univ _, ?_⟩
          funext j
          dsimp only [f]
          split_ifs with hji
          · subst hji; rfl
          · exact hz1 j hji
        · simp [hz1]
      rw [← Finset.sum_subset (Finset.subset_univ (Finset.image f Finset.univ))
        (fun z _ hz => hother z hz)]
      rw [Finset.sum_image]
      · refine Finset.sum_congr rfl fun b _ => ?_
        have h1 : ∀ j, j ≠ i → x j = f b j := fun j hj => by simp [f, hj]
        have h2 : ∀ j, j ≠ i → f b j = y j := fun j hj => by simp [f, hj, h j hj]
        dsimp only [f]
        rw [if_pos h1, if_pos h2]
        simp
      · intro a _ b _ hab
        have := congr_fun hab i
        simpa [f] using this
    exact hsum
  · simp only [if_neg h, mul_zero]
    refine Finset.sum_eq_zero fun z _ => ?_
    by_cases h1 : ∀ j, j ≠ i → x j = z j
    · by_cases h2 : ∀ j, j ≠ i → z j = y j
      · exfalso; exact h fun j hj => (h1 j hj).trans (h2 j hj)
      · simp [h2]
    · simp [h1]

private lemma onSite_comm {n : ℕ} {i j : Fin n} (hij : i ≠ j)
    (σ τ : Matrix (Fin 2) (Fin 2) ℂ) :
    onSite i σ * onSite j τ = onSite j τ * onSite i σ := by
  ext x y
  simp only [Matrix.mul_apply, onSite]
  by_cases h : ∀ k, k ≠ i → k ≠ j → x k = y k
  · let z1 : Config n := fun k => if k = i then y i else x k
    let z2 : Config n := fun k => if k = j then y j else x k
    have hs1 : (∑ z : Config n,
        (σ (x i) (z i) * if ∀ k, k ≠ i → x k = z k then (1 : ℂ) else 0) *
          (τ (z j) (y j) * if ∀ k, k ≠ j → z k = y k then (1 : ℂ) else 0)) =
        σ (x i) (y i) * τ (x j) (y j) := by
      rw [Finset.sum_eq_single z1]
      · have h1 : ∀ k, k ≠ i → x k = z1 k := fun k hk => by simp [z1, hk]
        have h2 : ∀ k, k ≠ j → z1 k = y k := fun k hk => by
          by_cases hki : k = i
          · subst hki; simp [z1]
          · simp [z1, hki, h k hki hk]
        rw [if_pos h1, if_pos h2]
        simp [z1, hij.symm]
      · intro z _ hz
        by_cases h1 : ∀ k, k ≠ i → x k = z k
        · by_cases h2 : ∀ k, k ≠ j → z k = y k
          · exfalso; apply hz; ext k
            by_cases hki : k = i
            · subst hki; simp [z1, h2 k hij]
            · simp [z1, hki, h1 k hki]
          · simp [h2]
        · simp [h1]
      · intro hz; exact absurd (Finset.mem_univ z1) hz
    have hs2 : (∑ z : Config n,
        (τ (x j) (z j) * if ∀ k, k ≠ j → x k = z k then (1 : ℂ) else 0) *
          (σ (z i) (y i) * if ∀ k, k ≠ i → z k = y k then (1 : ℂ) else 0)) =
        τ (x j) (y j) * σ (x i) (y i) := by
      rw [Finset.sum_eq_single z2]
      · have h1 : ∀ k, k ≠ j → x k = z2 k := fun k hk => by simp [z2, hk]
        have h2 : ∀ k, k ≠ i → z2 k = y k := fun k hk => by
          by_cases hkj : k = j
          · subst hkj; simp [z2]
          · simp [z2, hkj, h k hk hkj]
        rw [if_pos h1, if_pos h2]
        simp [z2, hij]
      · intro z _ hz
        by_cases h1 : ∀ k, k ≠ j → x k = z k
        · by_cases h2 : ∀ k, k ≠ i → z k = y k
          · exfalso; apply hz; ext k
            by_cases hkj : k = j
            · subst hkj; simp [z2, h2 k hij.symm]
            · simp [z2, hkj, h1 k hkj]
          · simp [h2]
        · simp [h1]
      · intro hz; exact absurd (Finset.mem_univ z2) hz
    rw [hs1, hs2, mul_comm]
  · push Not at h
    rcases h with ⟨k, hki, hkj, hne⟩
    have hz1 : (∑ z : Config n,
        (σ (x i) (z i) * if ∀ m, m ≠ i → x m = z m then (1 : ℂ) else 0) *
          (τ (z j) (y j) * if ∀ m, m ≠ j → z m = y m then (1 : ℂ) else 0)) = 0 := by
      refine Finset.sum_eq_zero fun z _ => ?_
      by_cases h1 : ∀ m, m ≠ i → x m = z m
      · by_cases h2 : ∀ m, m ≠ j → z m = y m
        · exact absurd ((h1 k hki).trans (h2 k hkj)) hne
        · simp [h2]
      · simp [h1]
    have hz2 : (∑ z : Config n,
        (τ (x j) (z j) * if ∀ m, m ≠ j → x m = z m then (1 : ℂ) else 0) *
          (σ (z i) (y i) * if ∀ m, m ≠ i → z m = y m then (1 : ℂ) else 0)) = 0 := by
      refine Finset.sum_eq_zero fun z _ => ?_
      by_cases h1 : ∀ m, m ≠ j → x m = z m
      · by_cases h2 : ∀ m, m ≠ i → z m = y m
        · exact absurd ((h1 k hkj).trans (h2 k hki)) hne
        · simp [h2]
      · simp [h1]
    rw [hz1, hz2]

private lemma onSite_one {n : ℕ} (i : Fin n) : onSite i (1 : Matrix (Fin 2) (Fin 2) ℂ) = 1 := by
  ext x y
  simp only [onSite, Matrix.one_apply]
  by_cases h : x = y
  · subst h; simp
  · simp only [if_neg h]
    by_cases hxi : x i = y i
    · have hne : ¬ ∀ j, j ≠ i → x j = y j := by
        intro hall; apply h; funext j
        by_cases hji : j = i
        · subst hji; exact hxi
        · exact hall j hji
      simp [hxi, hne]
    · simp [hxi]

private noncomputable def pauliPair {n : ℕ} (i j : Fin n) : Op n :=
  onSite i pauliX * onSite j pauliX + onSite i pauliY * onSite j pauliY +
    onSite i pauliZ * onSite j pauliZ

private lemma pauliPair_herm {n : ℕ} {i j : Fin n} (hij : i ≠ j) :
    (pauliPair i j).IsHermitian := by
  unfold pauliPair
  refine Matrix.IsHermitian.add (Matrix.IsHermitian.add ?_ ?_) ?_
  · rw [Matrix.IsHermitian, Matrix.conjTranspose_mul, onSite_herm i pauliX pauliX_herm,
      onSite_herm j pauliX pauliX_herm, onSite_comm hij.symm]
  · rw [Matrix.IsHermitian, Matrix.conjTranspose_mul, onSite_herm i pauliY pauliY_herm,
      onSite_herm j pauliY pauliY_herm, onSite_comm hij.symm]
  · rw [Matrix.IsHermitian, Matrix.conjTranspose_mul, onSite_herm i pauliZ pauliZ_herm,
      onSite_herm j pauliZ pauliZ_herm, onSite_comm hij.symm]

private lemma pauliPair_sq {n : ℕ} {i j : Fin n} (hij : i ≠ j) :
    pauliPair i j * pauliPair i j = (3 : ℂ) • 1 - (2 : ℂ) • pauliPair i j := by
  have hx := onSite_mul_same i pauliX pauliX
  have hy := onSite_mul_same i pauliY pauliY
  have hz := onSite_mul_same i pauliZ pauliZ
  have hxj := onSite_mul_same j pauliX pauliX
  have hyj := onSite_mul_same j pauliY pauliY
  have hzj := onSite_mul_same j pauliZ pauliZ
  rw [pauliX_sq, onSite_one] at hx hxj
  rw [pauliY_sq, onSite_one] at hy hyj
  rw [pauliZ_sq, onSite_one] at hz hzj
  have hXY : onSite i pauliX * onSite j pauliX * (onSite i pauliY * onSite j pauliY) =
      -(onSite i pauliZ * onSite j pauliZ) := by
    calc onSite i pauliX * onSite j pauliX * (onSite i pauliY * onSite j pauliY)
        = (onSite i pauliX * onSite i pauliY) * (onSite j pauliX * onSite j pauliY) := by
          simp only [Matrix.mul_assoc]
          congr 1
          rw [← Matrix.mul_assoc (onSite j pauliX), onSite_comm hij.symm, Matrix.mul_assoc]
      _ = onSite i (pauliX * pauliY) * onSite j (pauliX * pauliY) := by
          rw [onSite_mul_same, onSite_mul_same]
      _ = onSite i (Complex.I • pauliZ) * onSite j (Complex.I • pauliZ) := by
          have hxy : pauliX * pauliY = Complex.I • pauliZ := by
            ext a b; fin_cases a <;> fin_cases b <;> simp [pauliX, pauliY, pauliZ, Matrix.mul_apply]
          rw [hxy]
      _ = -(onSite i pauliZ * onSite j pauliZ) := by
          have hsm : ∀ (k : Fin n) (c : ℂ) (σ : Matrix (Fin 2) (Fin 2) ℂ),
              onSite k (c • σ) = c • onSite k σ := by
            intro k c σ; ext x y; simp [onSite, mul_assoc]
          rw [hsm, hsm, Matrix.smul_mul, Matrix.mul_smul, smul_smul, Complex.I_mul_I, neg_one_smul]
  have hYX : onSite i pauliY * onSite j pauliY * (onSite i pauliX * onSite j pauliX) =
      -(onSite i pauliZ * onSite j pauliZ) := by
    calc onSite i pauliY * onSite j pauliY * (onSite i pauliX * onSite j pauliX)
        = (onSite i pauliY * onSite i pauliX) * (onSite j pauliY * onSite j pauliX) := by
          simp only [Matrix.mul_assoc]; congr 1
          rw [← Matrix.mul_assoc (onSite j pauliY), onSite_comm hij.symm, Matrix.mul_assoc]
      _ = onSite i (pauliY * pauliX) * onSite j (pauliY * pauliX) := by
          rw [onSite_mul_same, onSite_mul_same]
      _ = onSite i ((-Complex.I) • pauliZ) * onSite j ((-Complex.I) • pauliZ) := by
          have hyx : pauliY * pauliX = (-Complex.I) • pauliZ := by
            ext a b; fin_cases a <;> fin_cases b <;> simp [pauliX, pauliY, pauliZ, Matrix.mul_apply]
          rw [hyx]
      _ = -(onSite i pauliZ * onSite j pauliZ) := by
          have hsm : ∀ (k : Fin n) (c : ℂ) (σ : Matrix (Fin 2) (Fin 2) ℂ),
              onSite k (c • σ) = c • onSite k σ := by
            intro k c σ; ext x y; simp [onSite, mul_assoc]
          rw [hsm, hsm, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
          simp [Complex.I_sq]
  have hYZ : onSite i pauliY * onSite j pauliY * (onSite i pauliZ * onSite j pauliZ) =
      -(onSite i pauliX * onSite j pauliX) := by
    calc onSite i pauliY * onSite j pauliY * (onSite i pauliZ * onSite j pauliZ)
        = (onSite i pauliY * onSite i pauliZ) * (onSite j pauliY * onSite j pauliZ) := by
          simp only [Matrix.mul_assoc]; congr 1
          rw [← Matrix.mul_assoc (onSite j pauliY), onSite_comm hij.symm, Matrix.mul_assoc]
      _ = onSite i (pauliY * pauliZ) * onSite j (pauliY * pauliZ) := by
          rw [onSite_mul_same, onSite_mul_same]
      _ = onSite i (Complex.I • pauliX) * onSite j (Complex.I • pauliX) := by
          have hyz : pauliY * pauliZ = Complex.I • pauliX := by
            ext a b; fin_cases a <;> fin_cases b <;> simp [pauliX, pauliY, pauliZ, Matrix.mul_apply]
          rw [hyz]
      _ = -(onSite i pauliX * onSite j pauliX) := by
          have hsm : ∀ (k : Fin n) (c : ℂ) (σ : Matrix (Fin 2) (Fin 2) ℂ),
              onSite k (c • σ) = c • onSite k σ := by
            intro k c σ; ext x y; simp [onSite, mul_assoc]
          rw [hsm, hsm, Matrix.smul_mul, Matrix.mul_smul, smul_smul, Complex.I_mul_I, neg_one_smul]
  have hZY : onSite i pauliZ * onSite j pauliZ * (onSite i pauliY * onSite j pauliY) =
      -(onSite i pauliX * onSite j pauliX) := by
    calc onSite i pauliZ * onSite j pauliZ * (onSite i pauliY * onSite j pauliY)
        = (onSite i pauliZ * onSite i pauliY) * (onSite j pauliZ * onSite j pauliY) := by
          simp only [Matrix.mul_assoc]; congr 1
          rw [← Matrix.mul_assoc (onSite j pauliZ), onSite_comm hij.symm, Matrix.mul_assoc]
      _ = onSite i (pauliZ * pauliY) * onSite j (pauliZ * pauliY) := by
          rw [onSite_mul_same, onSite_mul_same]
      _ = onSite i ((-Complex.I) • pauliX) * onSite j ((-Complex.I) • pauliX) := by
          have hzy : pauliZ * pauliY = (-Complex.I) • pauliX := by
            ext a b; fin_cases a <;> fin_cases b <;> simp [pauliX, pauliY, pauliZ, Matrix.mul_apply]
          rw [hzy]
      _ = -(onSite i pauliX * onSite j pauliX) := by
          have hsm : ∀ (k : Fin n) (c : ℂ) (σ : Matrix (Fin 2) (Fin 2) ℂ),
              onSite k (c • σ) = c • onSite k σ := by
            intro k c σ; ext x y; simp [onSite, mul_assoc]
          rw [hsm, hsm, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
          simp [Complex.I_sq]
  have hZX : onSite i pauliZ * onSite j pauliZ * (onSite i pauliX * onSite j pauliX) =
      -(onSite i pauliY * onSite j pauliY) := by
    calc onSite i pauliZ * onSite j pauliZ * (onSite i pauliX * onSite j pauliX)
        = (onSite i pauliZ * onSite i pauliX) * (onSite j pauliZ * onSite j pauliX) := by
          simp only [Matrix.mul_assoc]; congr 1
          rw [← Matrix.mul_assoc (onSite j pauliZ), onSite_comm hij.symm, Matrix.mul_assoc]
      _ = onSite i (pauliZ * pauliX) * onSite j (pauliZ * pauliX) := by
          rw [onSite_mul_same, onSite_mul_same]
      _ = onSite i (Complex.I • pauliY) * onSite j (Complex.I • pauliY) := by
          have hzx : pauliZ * pauliX = Complex.I • pauliY := by
            ext a b; fin_cases a <;> fin_cases b <;> simp [pauliX, pauliY, pauliZ, Matrix.mul_apply]
          rw [hzx]
      _ = -(onSite i pauliY * onSite j pauliY) := by
          have hsm : ∀ (k : Fin n) (c : ℂ) (σ : Matrix (Fin 2) (Fin 2) ℂ),
              onSite k (c • σ) = c • onSite k σ := by
            intro k c σ; ext x y; simp [onSite, mul_assoc]
          rw [hsm, hsm, Matrix.smul_mul, Matrix.mul_smul, smul_smul, Complex.I_mul_I, neg_one_smul]
  have hXZ : onSite i pauliX * onSite j pauliX * (onSite i pauliZ * onSite j pauliZ) =
      -(onSite i pauliY * onSite j pauliY) := by
    calc onSite i pauliX * onSite j pauliX * (onSite i pauliZ * onSite j pauliZ)
        = (onSite i pauliX * onSite i pauliZ) * (onSite j pauliX * onSite j pauliZ) := by
          simp only [Matrix.mul_assoc]; congr 1
          rw [← Matrix.mul_assoc (onSite j pauliX), onSite_comm hij.symm, Matrix.mul_assoc]
      _ = onSite i (pauliX * pauliZ) * onSite j (pauliX * pauliZ) := by
          rw [onSite_mul_same, onSite_mul_same]
      _ = onSite i ((-Complex.I) • pauliY) * onSite j ((-Complex.I) • pauliY) := by
          have hxz : pauliX * pauliZ = (-Complex.I) • pauliY := by
            ext a b; fin_cases a <;> fin_cases b <;> simp [pauliX, pauliY, pauliZ, Matrix.mul_apply]
          rw [hxz]
      _ = -(onSite i pauliY * onSite j pauliY) := by
          have hsm : ∀ (k : Fin n) (c : ℂ) (σ : Matrix (Fin 2) (Fin 2) ℂ),
              onSite k (c • σ) = c • onSite k σ := by
            intro k c σ; ext x y; simp [onSite, mul_assoc]
          rw [hsm, hsm, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
          simp [Complex.I_sq]
  have hXX : (onSite i pauliX * onSite j pauliX) * (onSite i pauliX * onSite j pauliX) = 1 := by
    calc (onSite i pauliX * onSite j pauliX) * (onSite i pauliX * onSite j pauliX)
        = (onSite i pauliX * onSite i pauliX) * (onSite j pauliX * onSite j pauliX) := by
          simp only [Matrix.mul_assoc]; congr 1
          rw [← Matrix.mul_assoc (onSite j pauliX), onSite_comm hij.symm, Matrix.mul_assoc]
      _ = 1 := by rw [hx, hxj, one_mul]
  have hYY : (onSite i pauliY * onSite j pauliY) * (onSite i pauliY * onSite j pauliY) = 1 := by
    calc (onSite i pauliY * onSite j pauliY) * (onSite i pauliY * onSite j pauliY)
        = (onSite i pauliY * onSite i pauliY) * (onSite j pauliY * onSite j pauliY) := by
          simp only [Matrix.mul_assoc]; congr 1
          rw [← Matrix.mul_assoc (onSite j pauliY), onSite_comm hij.symm, Matrix.mul_assoc]
      _ = 1 := by rw [hy, hyj, one_mul]
  have hZZ : (onSite i pauliZ * onSite j pauliZ) * (onSite i pauliZ * onSite j pauliZ) = 1 := by
    calc (onSite i pauliZ * onSite j pauliZ) * (onSite i pauliZ * onSite j pauliZ)
        = (onSite i pauliZ * onSite i pauliZ) * (onSite j pauliZ * onSite j pauliZ) := by
          simp only [Matrix.mul_assoc]; congr 1
          rw [← Matrix.mul_assoc (onSite j pauliZ), onSite_comm hij.symm, Matrix.mul_assoc]
      _ = 1 := by rw [hz, hzj, one_mul]
  unfold pauliPair
  simp only [Matrix.add_mul, Matrix.mul_add, hXX, hYY, hZZ, hXY, hYX, hYZ, hZY, hZX, hXZ]
  ext x y
  simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.neg_apply, smul_eq_mul]
  ring

private lemma pauliPair_anticomm_symm {n : ℕ} {c j k : Fin n}
    (hcj : c ≠ j) (hck : c ≠ k) (hjk : j ≠ k) :
    pauliPair c j * pauliPair c k + pauliPair c k * pauliPair c j = (2 : ℂ) • pauliPair j k := by
  have h1 : ∀ (σ τ : Matrix (Fin 2) (Fin 2) ℂ), σ * τ + τ * σ = 0 →
      (onSite c σ * onSite j σ) * (onSite c τ * onSite k τ) +
      (onSite c τ * onSite k τ) * (onSite c σ * onSite j σ) = 0 := by
    intro σ τ hanti
    have hL : (onSite c σ * onSite j σ) * (onSite c τ * onSite k τ) =
        onSite c (σ * τ) * onSite j σ * onSite k τ := by
      rw [Matrix.mul_assoc (onSite c σ), ← Matrix.mul_assoc (onSite j σ) (onSite c τ),
          onSite_comm hcj.symm, ← Matrix.mul_assoc (onSite c σ), ← Matrix.mul_assoc (onSite c σ),
          onSite_mul_same]
    have hR : (onSite c τ * onSite k τ) * (onSite c σ * onSite j σ) =
        onSite c (τ * σ) * onSite j σ * onSite k τ := by
      rw [Matrix.mul_assoc (onSite c τ), ← Matrix.mul_assoc (onSite k τ) (onSite c σ),
          onSite_comm hck.symm, ← Matrix.mul_assoc (onSite c τ), ← Matrix.mul_assoc (onSite c τ),
          onSite_mul_same, Matrix.mul_assoc (onSite c (τ * σ)), onSite_comm hjk.symm,
          ← Matrix.mul_assoc]
    rw [hL, hR]
    calc onSite c (σ * τ) * onSite j σ * onSite k τ + onSite c (τ * σ) * onSite j σ * onSite k τ
        = (onSite c (σ * τ) + onSite c (τ * σ)) * onSite j σ * onSite k τ := by
          simp only [Matrix.add_mul]
      _ = onSite c (σ * τ + τ * σ) * onSite j σ * onSite k τ := by
          have hadd : onSite c (σ * τ) + onSite c (τ * σ) = onSite c (σ * τ + τ * σ) := by
            ext x y; simp only [Matrix.add_apply, onSite]; split_ifs <;> simp
          rw [hadd]
      _ = 0 := by
          rw [hanti]
          have hz : onSite c (0 : Matrix (Fin 2) (Fin 2) ℂ) = 0 := by ext x y; simp [onSite]
          rw [hz, Matrix.zero_mul, Matrix.zero_mul]
  have hsame : ∀ (a b : Fin n) (hca : c ≠ a) (σ : Matrix (Fin 2) (Fin 2) ℂ), σ * σ = 1 →
      (onSite c σ * onSite a σ) * (onSite c σ * onSite b σ) = onSite a σ * onSite b σ := by
    intro a b hca σ hsq
    rw [Matrix.mul_assoc (onSite c σ), ← Matrix.mul_assoc (onSite a σ) (onSite c σ),
        onSite_comm hca.symm, ← Matrix.mul_assoc (onSite c σ), ← Matrix.mul_assoc (onSite c σ),
        onSite_mul_same, hsq, onSite_one, one_mul]
  unfold pauliPair
  simp only [Matrix.add_mul, Matrix.mul_add, hsame j k hcj pauliX pauliX_sq,
    hsame j k hcj pauliY pauliY_sq, hsame j k hcj pauliZ pauliZ_sq,
    hsame k j hck pauliX pauliX_sq, hsame k j hck pauliY pauliY_sq,
    hsame k j hck pauliZ pauliZ_sq]
  have hXY := h1 pauliX pauliY pauliXY_anti
  have hXZ := h1 pauliX pauliZ pauliXZ_anti
  have hYZ := h1 pauliY pauliZ pauliYZ_anti
  have hYX := h1 pauliY pauliX (by rw [add_comm]; exact pauliXY_anti)
  have hZX := h1 pauliZ pauliX (by rw [add_comm]; exact pauliXZ_anti)
  have hZY := h1 pauliZ pauliY (by rw [add_comm]; exact pauliYZ_anti)
  have hcomX : onSite k pauliX * onSite j pauliX = onSite j pauliX * onSite k pauliX :=
    onSite_comm hjk.symm _ _
  have hcomY : onSite k pauliY * onSite j pauliY = onSite j pauliY * onSite k pauliY :=
    onSite_comm hjk.symm _ _
  have hcomZ : onSite k pauliZ * onSite j pauliZ = onSite j pauliZ * onSite k pauliZ :=
    onSite_comm hjk.symm _ _
  ext x y
  have eXY := congr_fun (congr_fun hXY x) y
  have eXZ := congr_fun (congr_fun hXZ x) y
  have eYZ := congr_fun (congr_fun hYZ x) y
  have eYX := congr_fun (congr_fun hYX x) y
  have eZX := congr_fun (congr_fun hZX x) y
  have eZY := congr_fun (congr_fun hZY x) y
  have cX := congr_fun (congr_fun hcomX x) y
  have cY := congr_fun (congr_fun hcomY x) y
  have cZ := congr_fun (congr_fun hcomZ x) y
  simp only [Matrix.add_apply, Matrix.zero_apply, Matrix.smul_apply, smul_eq_mul] at *
  linear_combination eXY + eXZ + eYZ + eYX + eZX + eZY + cX + cY + cZ

private lemma edgeTerm_eq {n : ℕ} (i j : Fin n) :
    edgeTerm i j = (1 / 2 : ℂ) • (1 - pauliPair i j) := by
  unfold edgeTerm pauliPair
  simp only [sub_add_eq_sub_sub]

private lemma energy_sq_nonneg {n : ℕ} (H : Op n) (hH : H.IsHermitian) (ψ : Config n → ℂ) :
    energy (H * H) ψ = ∑ x : Config n, ‖(H *ᵥ ψ) x‖ ^ 2 := by
  unfold energy
  have h1 : star ψ ⬝ᵥ ((H * H) *ᵥ ψ) = star (H *ᵥ ψ) ⬝ᵥ (H *ᵥ ψ) := by
    rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec]
    have hst : star ψ ᵥ* H = star (H *ᵥ ψ) := by
      ext x
      simp only [Matrix.vecMul, Matrix.mulVec, dotProduct, Pi.star_apply, Complex.star_def,
        map_sum]
      refine Finset.sum_congr rfl fun y _ => ?_
      rw [map_mul]
      have := congr_fun (congr_fun hH y) x
      simp only [Matrix.conjTranspose_apply, Complex.star_def] at this
      rw [this, mul_comm]
    rw [hst]
  rw [h1]
  simp only [dotProduct, Pi.star_apply, Complex.star_def, Complex.re_sum]
  simp_rw [mul_comm (starRingEnd ℂ _), Complex.mul_conj, Complex.ofReal_re,
    Complex.normSq_eq_norm_sq]

private lemma energy_pauliPair_le_one {n : ℕ} {j k : Fin n} (hjk : j ≠ k)
    (ψ : Config n → ℂ) (hψ : IsUnitState ψ) :
    energy (pauliPair j k) ψ ≤ 1 := by
  have hherm : (edgeTerm j k).IsHermitian := by
    rw [edgeTerm_eq, Matrix.IsHermitian, Matrix.conjTranspose_smul, Matrix.conjTranspose_sub,
        Matrix.conjTranspose_one, pauliPair_herm hjk]
    simp
  have hsq : edgeTerm j k * edgeTerm j k = (2 : ℂ) • edgeTerm j k := by
    rw [edgeTerm_eq, Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.sub_mul, Matrix.mul_sub,
        Matrix.one_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, pauliPair_sq hjk]
    ext x y
    simp only [Matrix.smul_apply, Matrix.sub_apply, Matrix.add_apply, Matrix.one_apply, smul_eq_mul]
    ring
  have hnn : 0 ≤ energy (edgeTerm j k) ψ := by
    have he := energy_sq_nonneg (edgeTerm j k) hherm ψ
    rw [hsq] at he
    have h2 : energy ((2 : ℂ) • edgeTerm j k) ψ = 2 * energy (edgeTerm j k) ψ := by
      unfold energy
      rw [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]
      simp [Complex.mul_re]
    rw [h2] at he
    have hsum : 0 ≤ ∑ x : Config n, ‖(edgeTerm j k *ᵥ ψ) x‖ ^ 2 :=
      Finset.sum_nonneg fun x _ => sq_nonneg _
    linarith
  have heq : energy (edgeTerm j k) ψ = (1 - energy (pauliPair j k) ψ) / 2 := by
    rw [edgeTerm_eq]
    unfold energy
    rw [Matrix.smul_mulVec, dotProduct_smul, Matrix.sub_mulVec, Matrix.one_mulVec,
        dotProduct_sub, smul_eq_mul]
    have hunit : (star ψ ⬝ᵥ ψ).re = 1 := by
      simp only [dotProduct, Pi.star_apply, Complex.star_def, Complex.re_sum]
      simp_rw [mul_comm (starRingEnd ℂ (ψ _)), Complex.mul_conj, Complex.ofReal_re,
        Complex.normSq_eq_norm_sq]
      exact hψ
    set z := (star ψ ⬝ᵥ (pauliPair j k *ᵥ ψ)).re
    have h12 : ((1 / 2 : ℂ) * (star ψ ⬝ᵥ ψ - star ψ ⬝ᵥ (pauliPair j k *ᵥ ψ))).re = (1 - z) / 2 := by
      simp only [Complex.mul_re, Complex.sub_re, hunit]
      norm_num [z]
      ring
    exact h12
  set e1 := energy (edgeTerm j k) ψ
  set e2 := energy (pauliPair j k) ψ
  linarith

private lemma energy_cs {n : ℕ} (A : Op n) (hA : A.IsHermitian) (ψ : Config n → ℂ)
    (hψ : IsUnitState ψ) :
    (energy A ψ) ^ 2 ≤ energy (A * A) ψ := by
  rw [energy_sq_nonneg A hA ψ]
  have habs : |energy A ψ| ≤ ∑ x : Config n, ‖ψ x‖ * ‖(A *ᵥ ψ) x‖ := by
    unfold energy
    simp only [dotProduct, Pi.star_apply, Complex.star_def, Complex.re_sum]
    calc |∑ x : Config n, (starRingEnd ℂ (ψ x) * (A *ᵥ ψ) x).re|
        ≤ ∑ x : Config n, |(starRingEnd ℂ (ψ x) * (A *ᵥ ψ) x).re| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ x : Config n, ‖starRingEnd ℂ (ψ x) * (A *ᵥ ψ) x‖ :=
          Finset.sum_le_sum fun x _ => Complex.abs_re_le_norm _
      _ = ∑ x : Config n, ‖ψ x‖ * ‖(A *ᵥ ψ) x‖ := by
          refine Finset.sum_congr rfl fun x _ => ?_
          rw [norm_mul, Complex.norm_conj]
  have hsq1 : (energy A ψ) ^ 2 ≤ (∑ x : Config n, ‖ψ x‖ * ‖(A *ᵥ ψ) x‖) ^ 2 := by
    rw [← sq_abs (energy A ψ)]
    exact pow_le_pow_left₀ (abs_nonneg _) habs 2
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Config n))
    (fun x => ‖ψ x‖) (fun x => ‖(A *ᵥ ψ) x‖)
  have hunit : (∑ x : Config n, ‖ψ x‖ ^ 2) = 1 := hψ
  rw [hunit, one_mul] at hcs
  exact hsq1.trans hcs

private lemma energy_add {n : ℕ} (A B : Op n) (ψ : Config n → ℂ) :
    energy (A + B) ψ = energy A ψ + energy B ψ := by
  unfold energy
  rw [Matrix.add_mulVec, dotProduct_add, Complex.add_re]

private lemma energy_smul_real {n : ℕ} (r : ℝ) (A : Op n) (ψ : Config n → ℂ) :
    energy ((r : ℂ) • A) ψ = r * energy A ψ := by
  unfold energy
  rw [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul, Complex.re_ofReal_mul]

private lemma energy_sum {n : ℕ} {ι : Type*} (s : Finset ι) (f : ι → Op n) (ψ : Config n → ℂ) :
    energy (∑ i ∈ s, f i) ψ = ∑ i ∈ s, energy (f i) ψ := by
  classical
  induction s using Finset.induction with
  | empty => unfold energy; simp
  | @insert a s ha ih => rw [Finset.sum_insert ha, energy_add, ih, Finset.sum_insert ha]

private lemma energy_one {n : ℕ} (ψ : Config n → ℂ) (hψ : IsUnitState ψ) :
    energy (1 : Op n) ψ = 1 := by
  unfold energy
  rw [Matrix.one_mulVec]
  simp only [dotProduct, Pi.star_apply, Complex.star_def, Complex.re_sum]
  simp_rw [mul_comm (starRingEnd ℂ (ψ _)), Complex.mul_conj, Complex.ofReal_re,
    Complex.normSq_eq_norm_sq]
  exact hψ

private lemma energy_star_unweighted {n : ℕ} (c : Fin n) (S : Finset (Fin n))
    (hc : c ∉ S) (hS : S.Nonempty) (ψ : Config n → ℂ) (hψ : IsUnitState ψ) :
    ∑ j ∈ S, energy (edgeTerm c j) ψ ≤ (S.card : ℝ) + 1 := by
  let A : Op n := -∑ j ∈ S, pauliPair c j
  have hA_herm : A.IsHermitian := by
    rw [Matrix.IsHermitian, Matrix.conjTranspose_neg, Matrix.conjTranspose_sum]
    congr 1
    refine Finset.sum_congr rfl fun j hj => ?_
    have hcj : c ≠ j := fun h => hc (h ▸ hj)
    exact pauliPair_herm hcj
  have hAA : A * A =
      ∑ j ∈ S, ((3 : ℂ) • 1 - (2 : ℂ) • pauliPair c j) +
      ∑ j ∈ S, ∑ k ∈ S, (if j = k then 0 else pauliPair c j * pauliPair c k) := by
    dsimp only [A]
    rw [neg_mul_neg, Finset.sum_mul]
    simp_rw [Finset.mul_sum]
    have hsplit : ∀ j ∈ S,
        (∑ k ∈ S, pauliPair c j * pauliPair c k) =
        pauliPair c j * pauliPair c j +
          ∑ k ∈ S, (if j = k then 0 else pauliPair c j * pauliPair c k) := by
      intro j hj
      rw [← Finset.add_sum_erase S _ hj]
      conv_rhs => rhs; rw [← Finset.add_sum_erase S _ hj]
      simp only [↓reduceIte, zero_add]
      congr 1
      refine Finset.sum_congr rfl fun k hk => ?_
      have hjk : j ≠ k := (Finset.mem_erase.mp hk).1.symm
      simp [hjk]
    rw [Finset.sum_congr rfl hsplit, Finset.sum_add_distrib]
    congr 1
    refine Finset.sum_congr rfl fun j hj => ?_
    have hcj : c ≠ j := fun h => hc (h ▸ hj)
    exact pauliPair_sq hcj
  have hcross : (2 : ℝ) * energy
      (∑ j ∈ S, ∑ k ∈ S, (if j = k then 0 else pauliPair c j * pauliPair c k)) ψ =
      ∑ j ∈ S, ∑ k ∈ S, (if j = k then 0 else (2 : ℝ) * energy (pauliPair j k) ψ) := by
    have hsym : ((2 : ℝ) : ℂ) • (∑ j ∈ S, ∑ k ∈ S, (if j = k then 0 else pauliPair c j * pauliPair c k)) =
        ∑ j ∈ S, ∑ k ∈ S, (if j = k then 0 else ((2 : ℝ) : ℂ) • pauliPair j k) := by
      have hcomm_sum : (∑ j ∈ S, ∑ k ∈ S, (if j = k then 0 else pauliPair c j * pauliPair c k)) =
          ∑ j ∈ S, ∑ k ∈ S, (if j = k then 0 else pauliPair c k * pauliPair c j) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
        by_cases hjk : j = k
        · subst hjk; simp
        · simp [hjk, Ne.symm hjk]
      rw [show ((2 : ℝ) : ℂ) = 2 from by norm_num, two_smul]
      conv_lhs => rhs; rw [hcomm_sum]
      simp_rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun j hj => Finset.sum_congr rfl fun k hk => ?_
      by_cases hjk : j = k
      · subst hjk; simp
      · have hcj : c ≠ j := fun h => hc (h ▸ hj)
        have hck : c ≠ k := fun h => hc (h ▸ hk)
        simp only [if_neg hjk]
        exact pauliPair_anticomm_symm hcj hck hjk
    have h2 := congrArg (fun M => energy M ψ) hsym
    rw [energy_smul_real] at h2
    rw [h2, energy_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [energy_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    split_ifs with hjk
    · unfold energy; simp
    · rw [energy_smul_real]
  have hcross_le : energy
      (∑ j ∈ S, ∑ k ∈ S, (if j = k then 0 else pauliPair c j * pauliPair c k)) ψ ≤
      (S.card : ℝ) * ((S.card : ℝ) - 1) := by
    have hsum_le : (∑ j ∈ S, ∑ k ∈ S, (if j = k then 0 else (2 : ℝ) * energy (pauliPair j k) ψ)) ≤
        ∑ j ∈ S, ∑ k ∈ S, (if j = k then 0 else (2 : ℝ)) := by
      refine Finset.sum_le_sum fun j hj => Finset.sum_le_sum fun k hk => ?_
      split_ifs with hjk
      · exact le_rfl
      · linarith [energy_pauliPair_le_one hjk ψ hψ]
    have hsum_ones : (∑ j ∈ S, ∑ k ∈ S, (if j = k then (0 : ℝ) else 2)) =
        2 * ((S.card : ℝ) * ((S.card : ℝ) - 1)) := by
      have hrow : ∀ j ∈ S, (∑ k ∈ S, (if j = k then (0 : ℝ) else 2)) = 2 * ((S.card : ℝ) - 1) := by
        intro j hj
        rw [← Finset.add_sum_erase S _ hj]
        simp only [↓reduceIte, zero_add]
        have hconst : (∑ k ∈ S.erase j, (if j = k then (0 : ℝ) else 2)) =
            ∑ _ ∈ S.erase j, (2 : ℝ) := by
          refine Finset.sum_congr rfl fun k hk => ?_
          simp [(Finset.mem_erase.mp hk).1.symm]
        rw [hconst, Finset.sum_const, Finset.card_erase_of_mem hj, nsmul_eq_mul]
        have hpos : 1 ≤ S.card := Finset.card_pos.mpr hS
        rw [Nat.cast_sub hpos, Nat.cast_one]
        ring
      rw [Finset.sum_congr rfl hrow, Finset.sum_const, nsmul_eq_mul]
      ring
    linarith [hcross]
  have hAA_le : energy (A * A) ψ ≤ (S.card : ℝ) ^ 2 + 2 * (S.card : ℝ) + 2 * energy A ψ := by
    rw [hAA, energy_add, energy_sum]
    have hdiag : (∑ j ∈ S, energy ((3 : ℂ) • (1 : Op n) - (2 : ℂ) • pauliPair c j) ψ) =
        3 * (S.card : ℝ) + 2 * energy A ψ := by
      have hterm : ∀ j ∈ S, energy ((3 : ℂ) • (1 : Op n) - (2 : ℂ) • pauliPair c j) ψ =
          3 - 2 * energy (pauliPair c j) ψ := by
        intro j _
        rw [sub_eq_add_neg, energy_add, show (3 : ℂ) • (1 : Op n) = ((3 : ℝ) : ℂ) • 1 from rfl,
            energy_smul_real, energy_one ψ hψ,
            show -((2 : ℂ) • pauliPair c j) = ((-2 : ℝ) : ℂ) • pauliPair c j by ext x y; simp,
            energy_smul_real]
        ring
      rw [Finset.sum_congr rfl hterm, Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul,
          ← Finset.mul_sum]
      have hAe : energy A ψ = -∑ j ∈ S, energy (pauliPair c j) ψ := by
        dsimp only [A]
        unfold energy
        rw [Matrix.neg_mulVec, dotProduct_neg, Complex.neg_re]
        congr 1
        exact energy_sum S (pauliPair c) ψ
      set sumP := ∑ j ∈ S, energy (pauliPair c j) ψ
      set eA := energy A ψ
      linarith
    rw [hdiag]
    set eCross := energy (∑ j ∈ S, ∑ k ∈ S, (if j = k then 0 else pauliPair c j * pauliPair c k)) ψ
    set eA := energy A ψ
    set kR : ℝ := (S.card : ℝ)
    nlinarith
  have hcs := energy_cs A hA_herm ψ hψ
  have hA_le : energy A ψ ≤ (S.card : ℝ) + 2 := by
    set eA := energy A ψ
    set eAA := energy (A * A) ψ
    set kR : ℝ := (S.card : ℝ)
    have hkR : 0 ≤ kR := Nat.cast_nonneg _
    nlinarith [sq_nonneg (eA - (kR + 2))]
  have hedge : ∀ j ∈ S, energy (edgeTerm c j) ψ = (1 - energy (pauliPair c j) ψ) / 2 := by
    intro j _
    rw [edgeTerm_eq]
    unfold energy
    rw [Matrix.smul_mulVec, dotProduct_smul, Matrix.sub_mulVec, Matrix.one_mulVec,
        dotProduct_sub, smul_eq_mul]
    have hunit : (star ψ ⬝ᵥ ψ).re = 1 := by
      simp only [dotProduct, Pi.star_apply, Complex.star_def, Complex.re_sum]
      simp_rw [mul_comm (starRingEnd ℂ (ψ _)), Complex.mul_conj, Complex.ofReal_re,
        Complex.normSq_eq_norm_sq]
      exact hψ
    set z := (star ψ ⬝ᵥ (pauliPair c j *ᵥ ψ)).re
    have h12 : ((1 / 2 : ℂ) * (star ψ ⬝ᵥ ψ - star ψ ⬝ᵥ (pauliPair c j *ᵥ ψ))).re = (1 - z) / 2 := by
      simp only [Complex.mul_re, Complex.sub_re, hunit]
      norm_num [z]
      ring
    exact h12
  have hAe : energy A ψ = -∑ j ∈ S, energy (pauliPair c j) ψ := by
    dsimp only [A]
    unfold energy
    rw [Matrix.neg_mulVec, dotProduct_neg, Complex.neg_re]
    congr 1
    exact energy_sum S (pauliPair c) ψ
  rw [Finset.sum_congr rfl hedge, ← Finset.sum_div, Finset.sum_sub_distrib, Finset.sum_const,
      nsmul_eq_mul, mul_one]
  set eA := energy A ψ
  set sumP := ∑ j ∈ S, energy (pauliPair c j) ψ
  set kR : ℝ := (S.card : ℝ)
  linarith

private lemma energy_star_weighted {n : ℕ} (c : Fin n) (S : Finset (Fin n)) (hc : c ∉ S)
    (ψ : Config n → ℂ) (hψ : IsUnitState ψ) (m : ℕ) :
    ∀ (w' : Fin n → ℝ), (∀ j ∈ S, 0 ≤ w' j) → (S.filter fun j => 0 < w' j).card ≤ m →
      ∑ j ∈ S, w' j * energy (edgeTerm c j) ψ ≤
        (if h : S.Nonempty then S.sup' h w' else 0) + ∑ j ∈ S, w' j := by
  induction m with
  | zero =>
    intro w' hw' hcard
    have hzero : ∀ j ∈ S, w' j = 0 := by
      intro j hj
      by_contra hne
      have hpos : 0 < w' j := lt_of_le_of_ne (hw' j hj) (Ne.symm hne)
      have hmem : j ∈ S.filter fun j => 0 < w' j := Finset.mem_filter.mpr ⟨hj, hpos⟩
      have := Finset.card_pos.mpr ⟨j, hmem⟩
      omega
    rw [Finset.sum_eq_zero fun j hj => by rw [hzero j hj, zero_mul]]
    split_ifs with hS
    · have hsup : S.sup' hS w' = 0 := by
        apply le_antisymm
        · exact Finset.sup'_le hS _ fun j hj => (hzero j hj).le
        · obtain ⟨j, hj⟩ := hS
          exact (hzero j hj).symm.le.trans (Finset.le_sup' w' hj)
      rw [hsup, Finset.sum_eq_zero fun j hj => hzero j hj, add_zero]
    · simp [Finset.not_nonempty_iff_eq_empty.mp hS]
  | succ m ih =>
    intro w' hw' hcard
    let T := S.filter fun j => 0 < w' j
    by_cases hT : T.Nonempty
    · obtain ⟨j₀, hj₀, hmin⟩ := T.exists_min_image w' hT
      let m₀ := w' j₀
      have hm₀ : 0 < m₀ := (Finset.mem_filter.mp hj₀).2
      let w'' : Fin n → ℝ := fun j => if j ∈ T then w' j - m₀ else 0
      have hw'' : ∀ j ∈ S, 0 ≤ w'' j := by
        intro j hj
        dsimp only [w'']
        split_ifs with h
        · exact sub_nonneg.mpr (hmin j h)
        · exact le_rfl
      have hT'' : (S.filter fun j => 0 < w'' j) ⊆ T.erase j₀ := by
        intro j hj
        rw [Finset.mem_filter] at hj
        have hjT : j ∈ T := by
          by_contra hnot
          simp [w'', hnot] at hj
        rw [Finset.mem_erase]
        refine ⟨?_, hjT⟩
        intro hjj₀
        subst hjj₀
        simp [w'', hj₀, m₀] at hj
      have hcard'' : (S.filter fun j => 0 < w'' j).card ≤ m := by
        have h1 := Finset.card_le_card hT''
        rw [Finset.card_erase_of_mem hj₀] at h1
        have hT_card : T.card ≤ m + 1 := hcard
        omega
      have hIH := ih w'' hw'' hcard''
      have hS : S.Nonempty := ⟨j₀, (Finset.mem_filter.mp hj₀).1⟩
      have hsub_T : T ⊆ S := Finset.filter_subset _ _
      have hfilt : S.filter (fun j => j ∈ T) = T := by
        ext j; simp [T]
      have hsplit_e : ∑ j ∈ S, w' j * energy (edgeTerm c j) ψ =
          ∑ j ∈ S, w'' j * energy (edgeTerm c j) ψ + m₀ * ∑ j ∈ T, energy (edgeTerm c j) ψ := by
        have hw_eq : ∀ j ∈ S, w' j * energy (edgeTerm c j) ψ =
            w'' j * energy (edgeTerm c j) ψ + (if j ∈ T then m₀ * energy (edgeTerm c j) ψ else 0) := by
          intro j hj
          dsimp only [w'']
          split_ifs with hjT
          · ring
          · have h0 : w' j = 0 := by
              by_contra hne
              exact hjT (Finset.mem_filter.mpr ⟨hj, lt_of_le_of_ne (hw' j hj) (Ne.symm hne)⟩)
            simp [h0]
        rw [Finset.sum_congr rfl hw_eq, Finset.sum_add_distrib, ← Finset.sum_filter, hfilt,
            ← Finset.mul_sum]
      have hsplit_w : ∑ j ∈ S, w' j = ∑ j ∈ S, w'' j + m₀ * (T.card : ℝ) := by
        have hw_eq : ∀ j ∈ S, w' j = w'' j + (if j ∈ T then m₀ else 0) := by
          intro j hj
          dsimp only [w'']
          split_ifs with hjT
          · ring
          · have h0 : w' j = 0 := by
              by_contra hne
              exact hjT (Finset.mem_filter.mpr ⟨hj, lt_of_le_of_ne (hw' j hj) (Ne.symm hne)⟩)
            simp [h0]
        rw [Finset.sum_congr rfl hw_eq, Finset.sum_add_distrib]
        conv_lhs => rhs; rw [← Finset.sum_filter, hfilt, Finset.sum_const, nsmul_eq_mul]
        ring
      have hsup_eq : S.sup' hS w'' + m₀ = S.sup' hS w' := by
        apply le_antisymm
        · have : S.sup' hS w'' ≤ S.sup' hS w' - m₀ := by
            refine Finset.sup'_le hS _ fun j hj => ?_
            dsimp only [w'']
            split_ifs with hjT
            · exact sub_le_sub_right (Finset.le_sup' w' hj) m₀
            · have hj₀S : j₀ ∈ S := (Finset.mem_filter.mp hj₀).1
              have hle_sup : m₀ ≤ S.sup' hS w' := Finset.le_sup' w' hj₀S
              exact sub_nonneg.mpr hle_sup
          linarith
        · have : S.sup' hS w' ≤ S.sup' hS w'' + m₀ := by
            refine Finset.sup'_le hS _ fun j hj => ?_
            by_cases hjT : j ∈ T
            · have h1 := Finset.le_sup' w'' hj
              dsimp only [w''] at h1
              rw [if_pos hjT] at h1
              linarith
            · have h0 : w' j = 0 := by
                by_contra hne
                exact hjT (Finset.mem_filter.mpr ⟨hj, lt_of_le_of_ne (hw' j hj) (Ne.symm hne)⟩)
              have hnn : 0 ≤ S.sup' hS w'' := le_trans (hw'' j₀ (Finset.mem_filter.mp hj₀).1) (Finset.le_sup' w'' (Finset.mem_filter.mp hj₀).1)
              linarith
          exact this
      have hcT : c ∉ T := fun h => hc (hsub_T h)
      have hunw := energy_star_unweighted c T hcT hT ψ hψ
      have hmul : m₀ * ∑ j ∈ T, energy (edgeTerm c j) ψ ≤ m₀ * ((T.card : ℝ) + 1) :=
        mul_le_mul_of_nonneg_left hunw hm₀.le
      rw [hsplit_e, hsplit_w, dif_pos hS]
      rw [dif_pos hS] at hIH
      linarith
    · have hcard0 : (S.filter fun j => 0 < w' j).card ≤ m := by
        have hT0 : T = ∅ := Finset.not_nonempty_iff_eq_empty.mp hT
        change T.card ≤ m
        rw [hT0, Finset.card_empty]
        exact Nat.zero_le m
      exact ih w' hw' hcard0

private lemma edgeTerm_symm {n : ℕ} (i j : Fin n) : edgeTerm i j = edgeTerm j i := by
  unfold edgeTerm
  have hcomm : ∀ σ : Matrix (Fin 2) (Fin 2) ℂ,
      onSite i σ * onSite j σ = onSite j σ * onSite i σ := by
    intro σ
    by_cases hij : i = j
    · subst hij; rfl
    · exact onSite_comm hij σ σ
  rw [hcomm pauliX, hcomm pauliY, hcomm pauliZ]

theorem solution {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (w : Sym2 (Fin n) → ℝ) (hw : ∀ e, 0 ≤ w e) (c : Fin n) (hstar : IsStar G c)
    (ψ : Config n → ℂ) (hψ : IsUnitState ψ) :
    energy (hamiltonian G w) ψ ≤ maxEdgeWeight G w + totalWeight G w := by
  let N := G.neighborFinset c
  have hcN : c ∉ N := G.loopless.irrefl c ∘ (G.mem_neighborFinset c c).mp
  have hham : hamiltonian G w = ∑ j ∈ N, ((w s(c, j) : ℝ) : ℂ) • edgeTerm c j := by
    unfold hamiltonian
    have hsplit : ∀ i j : Fin n,
        (if i < j ∧ G.Adj i j then ((w s(i, j) : ℝ) : ℂ) • edgeTerm i j else 0) =
        (if i = c ∧ i < j ∧ G.Adj c j then ((w s(c, j) : ℝ) : ℂ) • edgeTerm c j else 0) +
        (if j = c ∧ i < j ∧ G.Adj i c then ((w s(c, i) : ℝ) : ℂ) • edgeTerm c i else 0) := by
      intro i j
      by_cases h1 : i < j ∧ G.Adj i j
      · rcases hstar i j h1.2 with rfl | rfl
        · simp [h1.1, h1.2, not_lt_of_gt h1.1]
        · simp [h1.1, h1.2, not_lt_of_gt h1.1, Sym2.eq_swap, edgeTerm_symm]
      · have h1' : ¬ (i = c ∧ i < j ∧ G.Adj c j) := fun ⟨rfl, a, b⟩ => h1 ⟨a, b⟩
        have h2' : ¬ (j = c ∧ i < j ∧ G.Adj i c) := fun ⟨rfl, a, b⟩ => h1 ⟨a, b⟩
        simp [h1, h1', h2']
    simp_rw [hsplit, Finset.sum_add_distrib]
    have h1 : (∑ i : Fin n, ∑ j : Fin n,
        if i = c ∧ i < j ∧ G.Adj c j then ((w s(c, j) : ℝ) : ℂ) • edgeTerm c j else 0) =
        ∑ j ∈ N.filter (c < ·), ((w s(c, j) : ℝ) : ℂ) • edgeTerm c j := by
      rw [Finset.sum_eq_single c]
      · simp only [true_and, N, ← Finset.sum_filter]
        refine Finset.sum_congr (by ext j; simp [G.mem_neighborFinset, and_comm]) fun _ _ => rfl
      · intro i _ hi
        refine Finset.sum_eq_zero fun j _ => by simp [hi]
      · intro hc; exact absurd (Finset.mem_univ c) hc
    have h2 : (∑ i : Fin n, ∑ j : Fin n,
        if j = c ∧ i < j ∧ G.Adj i c then ((w s(c, i) : ℝ) : ℂ) • edgeTerm c i else 0) =
        ∑ i ∈ N.filter (· < c), ((w s(c, i) : ℝ) : ℂ) • edgeTerm c i := by
      rw [Finset.sum_comm, Finset.sum_eq_single c]
      · simp only [true_and, N, ← Finset.sum_filter]
        refine Finset.sum_congr (by ext i; simp [G.mem_neighborFinset, G.adj_comm, and_comm]) fun _ _ => rfl
      · intro j _ hj
        refine Finset.sum_eq_zero fun i _ => by simp [hj]
      · intro hc; exact absurd (Finset.mem_univ c) hc
    rw [h1, h2]
    have hdisj : Disjoint (N.filter (c < ·)) (N.filter (· < c)) := by
      rw [Finset.disjoint_left]
      intro j h1 h2
      simp only [Finset.mem_filter] at h1 h2
      omega
    rw [← Finset.sum_union hdisj]
    refine Finset.sum_congr ?_ fun _ _ => rfl
    ext j
    simp only [Finset.mem_union, Finset.mem_filter, N, G.mem_neighborFinset]
    constructor
    · rintro (⟨h, _⟩ | ⟨h, _⟩) <;> exact h
    · intro h
      rcases lt_trichotomy c j with hlt | heq | hgt
      · left; exact ⟨h, hlt⟩
      · exact absurd heq (G.ne_of_adj h)
      · right; exact ⟨h, hgt⟩
  have hW : totalWeight G w = ∑ j ∈ N, w s(c, j) := by
    unfold totalWeight
    let f : Fin n → Sym2 (Fin n) := fun j => s(c, j)
    have himg : G.edgeFinset = N.image f := by
      ext e
      induction e using Sym2.ind with | _ a b =>
      simp only [SimpleGraph.mem_edgeFinset, Finset.mem_image, N, G.mem_neighborFinset, f]
      constructor
      · intro hadj
        rcases hstar a b hadj with rfl | rfl
        · exact ⟨b, hadj, rfl⟩
        · exact ⟨a, hadj.symm, Sym2.eq_swap⟩
      · rintro ⟨j, hj, heq⟩
        rw [← heq]; exact hj
    rw [himg, Finset.sum_image]
    intro a ha b hb hab
    have hca : c ≠ a := G.ne_of_adj ((G.mem_neighborFinset c a).mp ha)
    have hcb : c ≠ b := G.ne_of_adj ((G.mem_neighborFinset c b).mp hb)
    rcases Sym2.eq_iff.mp hab with ⟨_, rfl⟩ | ⟨h1, _⟩
    · rfl
    · exact absurd h1 hcb
  have hmax : (if h : N.Nonempty then N.sup' h (fun j => w s(c, j)) else 0) ≤ maxEdgeWeight G w := by
    split_ifs with hN
    · refine Finset.sup'_le hN _ fun j hj => ?_
      have he : s(c, j) ∈ G.edgeFinset :=
        G.mem_edgeFinset.mpr ((G.mem_neighborFinset c j).mp hj)
      unfold maxEdgeWeight
      have hle : (w s(c, j)).toNNReal ≤ G.edgeFinset.sup fun e => (w e).toNNReal :=
        Finset.le_sup (f := fun e => (w e).toNNReal) he
      have hle' : ((w s(c, j)).toNNReal : ℝ) ≤ ((G.edgeFinset.sup fun e => (w e).toNNReal : NNReal) : ℝ) :=
        NNReal.coe_le_coe.mpr hle
      rwa [Real.coe_toNNReal _ (hw _)] at hle'
    · unfold maxEdgeWeight
      exact NNReal.coe_nonneg _
  rw [hham, energy_sum]
  have he : ∀ j ∈ N, energy (((w s(c, j) : ℝ) : ℂ) • edgeTerm c j) ψ =
      w s(c, j) * energy (edgeTerm c j) ψ :=
    fun j _ => energy_smul_real _ _ _
  rw [Finset.sum_congr rfl he]
  have hbound := energy_star_weighted c N hcN ψ hψ N.card (fun j => w s(c, j))
    (fun j _ => hw _) (Finset.card_filter_le _ _)
  linarith

