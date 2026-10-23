-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Information100.P26.lemma_5_4
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T16:53:52.804634+00:00
-- url     : https://prove2.me/submissions/fcfbca28-5a8e-4c0f-aad5-e06374c04985

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P26

noncomputable section

open scoped Matrix ComplexOrder ComplexConjugate BigOperators


namespace X6P26F

open QAlgorithms.Papers.Independent.Information100.P26

theorem comm_herm {d m : ℕ} (E : Fin m → Matrix (Fin d) (Fin d) ℂ)
    (hE : ∑ n, (E n)ᴴ * E n = 1) (hU : ∑ n, E n * (E n)ᴴ = 1)
    (Z : Matrix (Fin d) (Fin d) ℂ) (hZ : Zᴴ = Z) (hfix : ∑ n, E n * Z * (E n)ᴴ = Z) (n : Fin m) :
    E n * Z = Z * E n := by
  let C : Fin m → Matrix (Fin d) (Fin d) ℂ := fun n => Z * E n - E n * Z
  have hC : ∀ n, (C n * (C n)ᴴ).trace =
      (Z * (E n * (E n)ᴴ) * Z).trace - (Z * (E n * Z * (E n)ᴴ)).trace -
        (E n * Z * (E n)ᴴ * Z).trace + (Z * Z * ((E n)ᴴ * E n)).trace := by
    intro n
    simp only [C, Matrix.conjTranspose_sub, Matrix.conjTranspose_mul, hZ, sub_mul, mul_sub,
      Matrix.trace_sub]
    have : (E n * Z * (Z * (E n)ᴴ)).trace = (Z * Z * ((E n)ᴴ * E n)).trace := by
      rw [show E n * Z * (Z * (E n)ᴴ) = (E n * (Z * Z)) * (E n)ᴴ by simp only [Matrix.mul_assoc],
        Matrix.trace_mul_comm, ← Matrix.mul_assoc, Matrix.trace_mul_comm]
    rw [this]; simp only [Matrix.mul_assoc]; ring
  have hsum : ∑ n, (C n * (C n)ᴴ).trace = 0 := by
    simp only [hC, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Matrix.trace_sum,
      ← Finset.mul_sum, ← Finset.sum_mul, hU, hE, hfix]
    simp
  have hnn : ∀ n ∈ Finset.univ, 0 ≤ (C n * (C n)ᴴ).trace :=
    fun n _ => (Matrix.posSemidef_self_mul_conjTranspose (C n)).trace_nonneg
  have h0 := (Finset.sum_eq_zero_iff_of_nonneg hnn).1 hsum n (Finset.mem_univ _)
  rw [Matrix.trace_mul_conjTranspose_self_eq_zero_iff] at h0
  exact (sub_eq_zero.1 h0).symm

theorem kraus_lin {d m : ℕ} (E : Fin m → Matrix (Fin d) (Fin d) ℂ) (X Y : Matrix (Fin d) (Fin d) ℂ)
    (a b : ℂ) : ∑ n, E n * (a • X + b • Y) * (E n)ᴴ =
      a • ∑ n, E n * X * (E n)ᴴ + b • ∑ n, E n * Y * (E n)ᴴ := by
  simp [Matrix.mul_add, Matrix.add_mul, Finset.sum_add_distrib, Finset.smul_sum]

theorem comm_all {d m : ℕ} (E : Fin m → Matrix (Fin d) (Fin d) ℂ)
    (hE : ∑ n, (E n)ᴴ * E n = 1) (hU : ∑ n, E n * (E n)ᴴ = 1)
    (Z : Matrix (Fin d) (Fin d) ℂ) (hfix : ∑ n, E n * Z * (E n)ᴴ = Z)
    (hfix' : ∑ n, E n * Zᴴ * (E n)ᴴ = Zᴴ) (n : Fin m) :
    E n * Z = Z * E n := by
  let H : Matrix (Fin d) (Fin d) ℂ := (1/2 : ℂ) • Z + (1/2 : ℂ) • Zᴴ
  let K : Matrix (Fin d) (Fin d) ℂ := (-Complex.I/2) • Z + (Complex.I/2) • Zᴴ
  have hZ : Z = H + Complex.I • K := by
    simp only [H, K, smul_add, smul_smul]
    ext i j; simp; ring_nf; simp [Complex.I_sq]; ring
  have hH : Hᴴ = H := by
    simp only [H, Matrix.conjTranspose_add, Matrix.conjTranspose_smul, Matrix.conjTranspose_conjTranspose]
    simp [add_comm]
  have hK : Kᴴ = K := by
    simp only [K, Matrix.conjTranspose_add, Matrix.conjTranspose_smul,
      Matrix.conjTranspose_conjTranspose]
    rw [add_comm]; congr 2 <;> simp [Complex.ext_iff]
  have fH : ∑ n, E n * H * (E n)ᴴ = H := by simp only [H]; rw [kraus_lin, hfix, hfix']
  have fK : ∑ n, E n * K * (E n)ᴴ = K := by simp only [K]; rw [kraus_lin, hfix, hfix']
  have c1 := comm_herm E hE hU H hH fH n
  have c2 := comm_herm E hE hU K hK fK n
  rw [hZ, Matrix.mul_add, Matrix.add_mul, c1, Matrix.mul_smul, Matrix.smul_mul, c2]

end X6P26F

open scoped Matrix ComplexOrder ComplexConjugate BigOperators


namespace X6P26G

open QAlgorithms.Papers.Independent.Information100.P26 X6P26F

theorem main {d r : ℕ} (t : Map d) (ht : UnitalChannel t)
    (A : Submodule ℂ (Mat d)) (hA : CStar A) (hfix : Fixes t A)
    (P : Fin r → Mat d) (hP : MinimalCentralFamily A P) :
    (∀ k l : Fin r, ∀ X : Mat d,
      ∃ Y : Mat d, applyMap t (P k * X * P l) = P k * Y * P l) ∧
    Reduces t (commutant (center (A : Set (Mat d)))) := by
  obtain ⟨m, E, hE, hΦ⟩ := ht.1
  have hE' : ∑ n, (E n)ᴴ * E n = 1 := hE
  have hΦ' : ∀ X : Mat d, applyMap t X = ∑ n, E n * X * (E n)ᴴ := fun X => hΦ X
  have hU : ∑ n, E n * (E n)ᴴ = 1 := by
    have := hΦ' 1; rw [ht.2] at this; simpa using this.symm
  have hc : ∀ Z ∈ A, ∀ n, E n * Z = Z * E n := by
    intro Z hZ n
    refine comm_all E hE' hU Z ?_ ?_ n
    · rw [← hΦ']; exact hfix Z hZ
    · rw [← hΦ']; exact hfix _ (hA.2.2 Z hZ)
  have hc' : ∀ Z ∈ A, ∀ n, (E n)ᴴ * Z = Z * (E n)ᴴ := by
    intro Z hZ n
    have := congrArg Matrix.conjTranspose (hc _ (hA.2.2 Z hZ) n)
    simpa [Matrix.conjTranspose_mul] using this.symm
  have hPA : ∀ k, P k ∈ A := fun k => (hP.2.1 k).1.1
  refine ⟨fun k l X => ⟨applyMap t X, ?_⟩, ?_, ?_⟩
  · rw [hΦ', hΦ', Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [show E n * (P k * X * P l) * (E n)ᴴ = (E n * P k) * X * (P l * (E n)ᴴ) by
        simp only [Matrix.mul_assoc],
      hc _ (hPA k), ← hc' _ (hPA l)]
    simp only [Matrix.mul_assoc]
  · intro X hX W hW
    have hWA : W ∈ A := hW.1
    rw [hΦ', Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    calc E n * X * (E n)ᴴ * W = E n * (X * W) * (E n)ᴴ := by
          rw [Matrix.mul_assoc, hc' _ hWA]; simp only [Matrix.mul_assoc]
      _ = W * (E n * X * (E n)ᴴ) := by
          rw [hX W hW, ← Matrix.mul_assoc, hc _ hWA]; simp only [Matrix.mul_assoc]
  · intro X hX Y hY
    let Y' : Mat d := ∑ n, (E n)ᴴ * Y * E n
    have hY' : Y' ∈ commutant (center (A : Set (Mat d))) := by
      intro W hW
      have hWA : W ∈ A := hW.1
      simp only [Y', Finset.sum_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun n _ => ?_
      calc (E n)ᴴ * Y * E n * W = (E n)ᴴ * (Y * W) * E n := by
            rw [Matrix.mul_assoc, hc _ hWA]; simp only [Matrix.mul_assoc]
        _ = W * ((E n)ᴴ * Y * E n) := by
            rw [hY W hW, ← Matrix.mul_assoc, hc' _ hWA]; simp only [Matrix.mul_assoc]
    have h0 := hX Y' hY'
    unfold matrixInner at h0 ⊢
    rw [← h0, hΦ']
    simp only [Y', Matrix.conjTranspose_sum, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose, Finset.mul_sum, Finset.sum_mul, Matrix.trace_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [show Yᴴ * (E n * X * (E n)ᴴ) = (Yᴴ * E n * X) * (E n)ᴴ by simp only [Matrix.mul_assoc],
      Matrix.trace_mul_comm]
    simp only [Matrix.mul_assoc]

end X6P26G

open QAlgorithms.Papers.Independent.Information100.P26 in
theorem solution {d r : ℕ} (hd : 0 < d) (t : Map d) (ht : UnitalChannel t)
    (A : Submodule ℂ (Mat d)) (hA : CStar A) (hfix : Fixes t A)
    (P : Fin r → Mat d) (hP : MinimalCentralFamily A P) :
    (∀ k l : Fin r, ∀ X : Mat d,
      ∃ Y : Mat d, applyMap t (P k * X * P l) = P k * Y * P l) ∧
    Reduces t (commutant (center (A : Set (Mat d)))) :=
  X6P26G.main t ht A hA hfix P hP

end
