-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Next46.P37.cayley_correspondence
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-20T16:50:02.673796+00:00
-- url     : https://prove2.me/submissions/95a2c8fe-cf6f-472e-97cd-2a4f08d6e91f

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P37
noncomputable section

open QAlgorithms.Papers.Independent.Dependency50.P10 (Phase sigma)
open QAlgorithms.Papers.Independent.Next46.P37
open Matrix

namespace G62C

variable {n : ℕ}

theorem ss : sigma n * sigma n = -1 := by
  simp only [sigma, fromBlocks_multiply]
  simp only [Matrix.zero_mul, Matrix.mul_zero, zero_add, add_zero, Matrix.mul_one, Matrix.mul_neg,
    Matrix.neg_mul, Matrix.one_mul]
  rw [← fromBlocks_one, fromBlocks_neg, neg_zero]

theorem st : (sigma n)ᵀ = -sigma n := by
  simp [sigma, fromBlocks_transpose, fromBlocks_neg]

theorem sinv : (sigma n)⁻¹ = -sigma n :=
  inv_eq_right_inv (by rw [Matrix.mul_neg, ss, neg_neg])

theorem sdet : IsUnit (sigma n).det :=
  isUnit_det_of_right_inverse (B := -sigma n) (by rw [Matrix.mul_neg, ss, neg_neg])

theorem J_eq : Matrix.J (Fin n) ℝ = -sigma n := by
  simp [Matrix.J, sigma, fromBlocks_neg]

theorem symp_iff (S : Matrix (Phase n) (Phase n) ℝ) :
    S ∈ symplecticGroup (Fin n) ℝ ↔ Sᵀ * sigma n * S = sigma n := by
  rw [SymplecticGroup.mem_iff', J_eq]
  constructor
  · intro h; have := congrArg Neg.neg h; simpa using this
  · intro h; simp [h]

theorem half (X : Matrix (Phase n) (Phase n) ℝ) : (1 / 2 : ℝ) • X + (1 / 2 : ℝ) • X = X := by
  rw [← add_smul]; norm_num

theorem r1 {ι : Type*} [Fintype ι] [DecidableEq ι] (s V N : Matrix ι ι ℝ) :
    s * (1 + V * s + 1) * (-s * N) = -(s * s) * N - s * V * (s * s) * N - (s * s) * N := by noncomm_ring

theorem r2 {ι : Type*} [Fintype ι] [DecidableEq ι] (s V N : Matrix ι ι ℝ) :
    -(-1 : Matrix ι ι ℝ) * N - s * V * (-1) * N - (-1) * N = N + s * (V * N) + N := by noncomm_ring

theorem r3 {ι : Type*} [Fintype ι] [DecidableEq ι] (A B V W s : Matrix ι ι ℝ) :
    A * (V - W - W * s * V) * B = A * (V * B) - (A * W) * B - (A * W) * s * (V * B) := by noncomm_ring

theorem r4 {ι : Type*} [Fintype ι] [DecidableEq ι] (W A Z B V : Matrix ι ι ℝ) :
    W * A * Z * (B * V) = W * (A * Z * B) * V := by noncomm_ring

theorem r5 {ι : Type*} [Fintype ι] [DecidableEq ι] (s V W : Matrix ι ι ℝ) :
    (1 - s * W) * s * (1 + V * s) = s + s * (V - W - W * s * V) * s := by noncomm_ring

/-- part 1 -/
theorem part1 (S : Matrix (Phase n) (Phase n) ℝ) (hS : S ∈ symplecticGroup (Fin n) ℝ)
    (hd : (S - 1).det ≠ 0) :
    (cayley S).IsSymm ∧ (cayley S - (1 / 2 : ℝ) • sigma n).det ≠ 0 ∧
      inverseCayley (cayley S) = S := by
  set σ := sigma n with hσ
  have hu : IsUnit (S - 1).det := isUnit_iff_ne_zero.2 hd
  set U := (S - 1)⁻¹ with hUdef
  have hU1 : (S - 1) * U = 1 := mul_nonsing_inv _ hu
  have hU2 : U * (S - 1) = 1 := nonsing_inv_mul _ hu
  have hSU : S * U = 1 + U := by
    have : (S - 1) * U = S * U - U := by noncomm_ring
    rw [hU1] at this; rw [← sub_eq_iff_eq_add.1 this.symm]
  have hc : cayley S = (1 / 2 : ℝ) • σ + σ * U := by
    rw [cayley]
    have : σ * (S + 1) * U = σ + σ * U + σ * U := by
      rw [Matrix.mul_assoc, Matrix.add_mul, hSU]; noncomm_ring
    rw [this, smul_add, smul_add, add_assoc, half]
  have hm : cayley S - (1 / 2 : ℝ) • σ = σ * U := by rw [hc]; abel
  have hp : cayley S + (1 / 2 : ℝ) • σ = σ + σ * U := by rw [hc, add_comm, ← add_assoc, half]
  have hUu : IsUnit U.det := isUnit_nonsing_inv_det _ hu
  refine ⟨?_, ?_, ?_⟩
  · -- symmetry
    have hsym := (symp_iff S).1 hS
    rw [← hσ] at hsym
    have hT2 : (Sᵀ - 1) * Uᵀ = 1 := by
      have := congrArg Matrix.transpose hU2
      rwa [transpose_mul, transpose_sub, transpose_one] at this
    have hT1 : Uᵀ * (Sᵀ - 1) = 1 := by
      have := congrArg Matrix.transpose hU1
      rwa [transpose_mul, transpose_sub, transpose_one] at this
    set Z := σ * U + Uᵀ * σ + σ with hZ
    have h0 : (Sᵀ - 1) * Z * (S - 1) = 0 := by
      have e : (Sᵀ - 1) * Z * (S - 1) =
          (Sᵀ - 1) * σ * (U * (S - 1)) + ((Sᵀ - 1) * Uᵀ) * σ * (S - 1) + (Sᵀ - 1) * σ * (S - 1) := by
        rw [hZ]; noncomm_ring
      rw [e, hU2, hT2]
      have e2 : (Sᵀ - 1) * σ * 1 + 1 * σ * (S - 1) + (Sᵀ - 1) * σ * (S - 1) = Sᵀ * σ * S - σ := by
        noncomm_ring
      rw [e2, hsym, sub_self]
    have hZ0 : Z = 0 := by
      have : Z = (Uᵀ * (Sᵀ - 1)) * Z * ((S - 1) * U) := by rw [hT1, hU1]; simp
      rw [this]
      have : Uᵀ * (Sᵀ - 1) * Z * ((S - 1) * U) = Uᵀ * ((Sᵀ - 1) * Z * (S - 1)) * U := by noncomm_ring
      rw [this, h0]; simp
    show (cayley S)ᵀ = cayley S
    rw [hc, transpose_add, transpose_smul, transpose_mul, st, ← hσ]
    have : σ * U = -(Uᵀ * σ) - σ := by
      rw [hZ] at hZ0
      rw [eq_sub_iff_add_eq, eq_neg_iff_add_eq_zero]; rw [← hZ0]; abel
    rw [this, Matrix.mul_neg]
    module
  · rw [hm, det_mul]
    exact (sdet.mul hUu).ne_zero
  · rw [inverseCayley, hm, hp, Matrix.mul_inv_rev, nonsing_inv_nonsing_inv _ hu, sinv]
    have e : (S - 1) * -σ * (σ + σ * U) = -((S - 1) * (σ * σ) * (1 + U)) := by noncomm_ring
    rw [e, ss]
    have e2 : -((S - 1) * -1 * (1 + U)) = (S - 1) + (S - 1) * U := by noncomm_ring
    rw [e2, hU1]; abel

theorem part2 (M : Matrix (Phase n) (Phase n) ℝ) (hd : (M - (1 / 2 : ℝ) • sigma n).det ≠ 0) :
    (inverseCayley M - 1).det ≠ 0 ∧ cayley (inverseCayley M) = M ∧
      (inverseCayley M ∈ symplecticGroup (Fin n) ℝ ↔ M.IsSymm) := by
  have hu : IsUnit (M - (1 / 2 : ℝ) • sigma n).det := isUnit_iff_ne_zero.2 hd
  set V := (M - (1 / 2 : ℝ) • sigma n)⁻¹ with hVdef
  have hV1 : (M - (1 / 2 : ℝ) • sigma n) * V = 1 := mul_nonsing_inv _ hu
  have hV2 : V * (M - (1 / 2 : ℝ) • sigma n) = 1 := nonsing_inv_mul _ hu
  have hVu : IsUnit V.det := isUnit_nonsing_inv_det _ hu
  have hR : inverseCayley M = 1 + V * sigma n := by
    rw [inverseCayley, ← hVdef]
    have : M + (1 / 2 : ℝ) • sigma n = (M - (1 / 2 : ℝ) • sigma n) + sigma n := by module
    rw [this, Matrix.mul_add, hV2]
  have hRm : inverseCayley M - 1 = V * sigma n := by rw [hR]; abel
  have hRd : (inverseCayley M - 1).det ≠ 0 := by
    rw [hRm, det_mul]; exact (hVu.mul sdet).ne_zero
  have hcay : cayley (inverseCayley M) = M := by
    rw [cayley, hRm, Matrix.mul_inv_rev, sinv, nonsing_inv_nonsing_inv _ hu, hR]
    rw [r1, ss, r2, hV2, Matrix.mul_one]
    module
  refine ⟨hRd, hcay, ⟨fun hs => ?_, fun hM => ?_⟩⟩
  · have := (part1 _ hs hRd).1
    rwa [hcay] at this
  · rw [symp_iff]
    have hMt : Mᵀ = M := hM
    obtain ⟨W, hW⟩ : ∃ W, W = Vᵀ := ⟨_, rfl⟩
    have hT : (M - (1 / 2 : ℝ) • sigma n)ᵀ = M + (1 / 2 : ℝ) • sigma n := by
      rw [transpose_sub, transpose_smul, st, hMt]; module
    have hW1 : W * (M + (1 / 2 : ℝ) • sigma n) = 1 := by
      have := congrArg Matrix.transpose hV1
      rwa [transpose_mul, hT, transpose_one, ← hW] at this
    have hW2 : (M + (1 / 2 : ℝ) • sigma n) * W = 1 := by
      have := congrArg Matrix.transpose hV2
      rwa [transpose_mul, hT, transpose_one, ← hW] at this
    set Z := V - W - W * sigma n * V with hZ
    have h0 : (M + (1 / 2 : ℝ) • sigma n) * Z * (M - (1 / 2 : ℝ) • sigma n) = 0 := by
      rw [hZ, r3, hV2, hW2]
      simp only [Matrix.mul_one, Matrix.one_mul]
      module
    have hZ0 : Z = 0 := by
      have : Z = (W * (M + (1 / 2 : ℝ) • sigma n)) * Z * ((M - (1 / 2 : ℝ) • sigma n) * V) := by
        rw [hW1, hV1]; simp
      rw [this]
      rw [r4, h0]; simp
    have hRt : (inverseCayley M)ᵀ = 1 - sigma n * W := by
      rw [hR, transpose_add, transpose_one, transpose_mul, st, ← hW, Matrix.neg_mul, ← sub_eq_add_neg]
    rw [hRt, hR]
    rw [r5, ← hZ, hZ0]; simp

end G62C

open QAlgorithms.Papers.Independent.Dependency50.P10 (Phase sigma)
open QAlgorithms.Papers.Independent.Next46.P37

theorem solution (n : ℕ) (hn : 0 < n) :
    (∀ S : Matrix (Phase n) (Phase n) ℝ,
      S ∈ Matrix.symplecticGroup (Fin n) ℝ → (S - 1).det ≠ 0 →
      (cayley S).IsSymm ∧
      (cayley S - (1 / 2 : ℝ) • sigma n).det ≠ 0 ∧
      inverseCayley (cayley S) = S) ∧
    (∀ M : Matrix (Phase n) (Phase n) ℝ,
      (M - (1 / 2 : ℝ) • sigma n).det ≠ 0 →
      (inverseCayley M - 1).det ≠ 0 ∧
      cayley (inverseCayley M) = M ∧
      (inverseCayley M ∈ Matrix.symplecticGroup (Fin n) ℝ ↔ M.IsSymm)) :=
  ⟨fun S hS hd => G62C.part1 S hS hd, fun M hd => G62C.part2 M hd⟩
