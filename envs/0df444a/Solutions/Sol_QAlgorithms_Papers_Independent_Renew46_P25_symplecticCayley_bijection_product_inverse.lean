-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Renew46.P25.symplecticCayley_bijection_product_inverse
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-20T23:58:14.856617+00:00
-- url     : https://prove2.me/submissions/32838dae-1071-4283-9da3-7d4d05229593

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P25
noncomputable section

open MeasureTheory

open QAlgorithms.Papers.Independent.Dependency50.P10 (Phase sigma)

open QAlgorithms.Papers.Independent.Next46.P37 (cayley inverseCayley diagonalHessian)

open Matrix
namespace g64g_C

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

end g64g_C
namespace g64g_C
variable {n : ℕ}

theorem cay_eq (S : Matrix (Phase n) (Phase n) ℝ) (hd : (S - 1).det ≠ 0) :
    cayley S = (1 / 2 : ℝ) • sigma n + sigma n * (S - 1)⁻¹ := by
  have hu : IsUnit (S - 1).det := isUnit_iff_ne_zero.2 hd
  have hU1 : (S - 1) * (S - 1)⁻¹ = 1 := mul_nonsing_inv _ hu
  have e : sigma n * (S + 1) * (S - 1)⁻¹ = sigma n * ((S - 1) * (S - 1)⁻¹) + sigma n * (S - 1)⁻¹ + sigma n * (S - 1)⁻¹ := by
    noncomm_ring
  rw [cayley, e, hU1, Matrix.mul_one, smul_add, smul_add, add_assoc, half]

theorem q1 {ι : Type*} [Fintype ι] [DecidableEq ι] (S T U V : Matrix ι ι ℝ) :
    U * (S * T - 1) * V = (U * (S - 1)) * ((T - 1) * V) + U * (S - 1) * V + U * ((T - 1) * V) := by
  noncomm_ring

theorem q2 {ι : Type*} [Fintype ι] [DecidableEq ι] (S T s U V W : Matrix ι ι ℝ) :
    -(T - 1) * W * (S - 1) * s * (s * U * (S * T - 1) * V) =
      -((T - 1) * W * (S - 1) * (s * s) * U * (S * T - 1) * V) := by
  noncomm_ring

theorem part3 (S T : Matrix (Phase n) (Phase n) ℝ)
    (hS : S ∈ Matrix.symplecticGroup (Fin n) ℝ)
    (hdS : (S - 1).det ≠ 0) (hdT : (T - 1).det ≠ 0) (hdST : (S * T - 1).det ≠ 0) :
    (cayley S + cayley T).det ≠ 0 ∧
      cayley (S * T) = cayley S + (S.transpose - 1)⁻¹ * sigma n *
        (cayley S + cayley T)⁻¹ * sigma n * (S - 1)⁻¹ ∧
      (cayley S + cayley T)⁻¹ = -(T - 1) * (S * T - 1)⁻¹ * (S - 1) * sigma n := by
  set σ := sigma n with hσ
  have huS : IsUnit (S - 1).det := isUnit_iff_ne_zero.2 hdS
  have huT : IsUnit (T - 1).det := isUnit_iff_ne_zero.2 hdT
  have huST : IsUnit (S * T - 1).det := isUnit_iff_ne_zero.2 hdST
  set U := (S - 1)⁻¹ with hU
  set V := (T - 1)⁻¹ with hV
  set W := (S * T - 1)⁻¹ with hW
  have hU1 : (S - 1) * U = 1 := mul_nonsing_inv _ huS
  have hU2 : U * (S - 1) = 1 := nonsing_inv_mul _ huS
  have hV1 : (T - 1) * V = 1 := mul_nonsing_inv _ huT
  have hW1 : (S * T - 1) * W = 1 := mul_nonsing_inv _ huST
  have hW2 : W * (S * T - 1) = 1 := nonsing_inv_mul _ huST
  have hsum : cayley S + cayley T = σ * U * (S * T - 1) * V := by
    rw [cay_eq S hdS, cay_eq T hdT, Matrix.mul_assoc σ U, Matrix.mul_assoc σ, q1, hU2, hV1]
    simp only [Matrix.one_mul, Matrix.mul_one]
    rw [← hσ]
    have : (1 / 2 : ℝ) • σ + σ * U + ((1 / 2 : ℝ) • σ + σ * V) =
        ((1 / 2 : ℝ) • σ + (1 / 2 : ℝ) • σ) + σ * U + σ * V := by abel
    rw [this, half]; noncomm_ring
  have hinv : (cayley S + cayley T)⁻¹ = -(T - 1) * W * (S - 1) * σ := by
    apply Matrix.inv_eq_left_inv
    rw [hsum, q2, ss]
    have : (T - 1) * W * (S - 1) * -1 * U * (S * T - 1) * V =
        -((T - 1) * (W * (((S - 1) * U) * (S * T - 1))) * V) := by noncomm_ring
    rw [this, hU1, Matrix.one_mul, hW2, Matrix.mul_one, hV1, neg_neg]
  refine ⟨?_, ?_, hinv⟩
  · rw [hsum, det_mul, det_mul, det_mul]
    exact (((sdet.mul (isUnit_nonsing_inv_det _ huS)).mul huST).mul
      (isUnit_nonsing_inv_det _ huT)).ne_zero
  · rw [hinv, cay_eq S hdS, cay_eq (S * T) hdST]
    -- key: (Sᵀ - 1) σ (1 + U) = -σ
    have hsym := (symp_iff S).1 hS
    rw [← hσ] at hsym
    have hUS : U * S = 1 + U := by
      have : U * (S - 1) = U * S - U := by noncomm_ring
      rw [hU2] at this; rw [← sub_eq_iff_eq_add.1 this.symm]
    have hkey : (Sᵀ - 1) * σ * (1 + U) = -σ := by
      have h1 : (Sᵀ - 1) * σ * (1 + U) * (S - 1) = -σ * (S - 1) := by
        have : (Sᵀ - 1) * σ * (1 + U) * (S - 1) = (Sᵀ - 1) * σ * (S - 1) + (Sᵀ - 1) * σ * (U * (S - 1)) := by
          noncomm_ring
        rw [this, hU2]
        have : (Sᵀ - 1) * σ * (S - 1) + (Sᵀ - 1) * σ * 1 = Sᵀ * σ * S - σ * S := by noncomm_ring
        rw [this, hsym]; noncomm_ring
      have := congrArg (· * U) h1
      simp only [Matrix.mul_assoc] at this
      rw [hU1, Matrix.mul_one, Matrix.mul_one] at this
      simpa only [Matrix.mul_assoc] using this
    have huSt : IsUnit (Sᵀ - 1).det := by
      rw [show Sᵀ - 1 = (S - 1)ᵀ by rw [transpose_sub, transpose_one], det_transpose]; exact huS
    set Y := (Sᵀ - 1)⁻¹ with hY
    have hY2 : Y * (Sᵀ - 1) = 1 := nonsing_inv_mul _ huSt
    -- W - U = -U S (T-1) W
    have hWU : W - U = -(1 + U) * (T - 1) * W := by
      have : W - U = U * (S - 1) * W - U * ((S * T - 1) * W) := by rw [hU2, hW1]; simp
      rw [this]
      have : U * (S - 1) * W - U * ((S * T - 1) * W) = -((U * S) * (T - 1) * W) := by noncomm_ring
      rw [this, hUS]; noncomm_ring
    have hYσ : Y * σ = -(σ * (1 + U)) := by
      calc Y * σ = Y * (-((Sᵀ - 1) * σ * (1 + U))) := by rw [hkey, neg_neg]
        _ = -((Y * (Sᵀ - 1)) * σ * (1 + U)) := by noncomm_ring
        _ = _ := by rw [hY2, Matrix.one_mul]
    rw [← hW, ← hU]
    have e : Y * σ * (-(T - 1) * W * (S - 1) * σ) * σ * U =
        -(Y * σ * (T - 1) * W * (S - 1) * (σ * σ) * U) := by noncomm_ring
    rw [e, ss]
    have e2 : -(Y * σ * (T - 1) * W * (S - 1) * -1 * U) = (Y * σ) * (T - 1) * W * ((S - 1) * U) := by
      noncomm_ring
    rw [e2, hU1, hYσ, Matrix.mul_one]
    have e3 : σ * W = σ * U + σ * (W - U) := by noncomm_ring
    rw [e3, hWU]; noncomm_ring

theorem part4 (S : Matrix (Phase n) (Phase n) ℝ) (hS : S ∈ Matrix.symplecticGroup (Fin n) ℝ)
    (hd : (S - 1).det ≠ 0) : (S⁻¹ - 1).det ≠ 0 ∧ cayley S⁻¹ = -cayley S := by
  have hSu : IsUnit S.det := SymplecticGroup.symplectic_det hS
  have hu : IsUnit (S - 1).det := isUnit_iff_ne_zero.2 hd
  have hS1 : S * S⁻¹ = 1 := mul_nonsing_inv _ hSu
  have hS2 : S⁻¹ * S = 1 := nonsing_inv_mul _ hSu
  have hfac : S⁻¹ - 1 = -(S⁻¹ * (S - 1)) := by
    rw [Matrix.mul_sub, hS2, Matrix.mul_one]; abel
  have hd' : (S⁻¹ - 1).det ≠ 0 := by
    rw [hfac, det_neg, det_mul]
    exact (((isUnit_neg_one (α := ℝ)).pow _).mul ((isUnit_nonsing_inv_det _ hSu).mul hu)).ne_zero
  refine ⟨hd', ?_⟩
  have hinv : (S⁻¹ - 1)⁻¹ = -((S - 1)⁻¹ * S) := by
    apply Matrix.inv_eq_left_inv
    rw [hfac]
    have : -((S - 1)⁻¹ * S) * -(S⁻¹ * (S - 1)) = (S - 1)⁻¹ * (S * S⁻¹) * (S - 1) := by noncomm_ring
    rw [this, hS1, Matrix.mul_one, nonsing_inv_mul _ hu]
  rw [cay_eq _ hd', cay_eq _ hd, hinv]
  have hUS : (S - 1)⁻¹ * S = 1 + (S - 1)⁻¹ := by
    have : (S - 1)⁻¹ * (S - 1) = (S - 1)⁻¹ * S - (S - 1)⁻¹ := by noncomm_ring
    rw [nonsing_inv_mul _ hu] at this; rw [← sub_eq_iff_eq_add.1 this.symm]
  rw [hUS]
  have : (1 / 2 : ℝ) • sigma n + sigma n * -(1 + (S - 1)⁻¹) =
      ((1 / 2 : ℝ) • sigma n - ((1 / 2 : ℝ) • sigma n + (1 / 2 : ℝ) • sigma n)) - sigma n * (S - 1)⁻¹ := by
    rw [half]; noncomm_ring
  rw [this]; module

end g64g_C

open QAlgorithms.Papers.Independent.Renew46.P25

theorem solution (n : ℕ) (hn : 0 < n) :
    (∀ S : Matrix (Phase n) (Phase n) ℝ,
      S ∈ Matrix.symplecticGroup (Fin n) ℝ → (S - 1).det ≠ 0 →
      (cayley S).IsSymm ∧ (cayley S - (1 / 2 : ℝ) • sigma n).det ≠ 0 ∧
        inverseCayley (cayley S) = S) ∧
    (∀ M : Matrix (Phase n) (Phase n) ℝ,
      M.IsSymm → (M - (1 / 2 : ℝ) • sigma n).det ≠ 0 →
      inverseCayley M ∈ Matrix.symplecticGroup (Fin n) ℝ ∧
        (inverseCayley M - 1).det ≠ 0 ∧ cayley (inverseCayley M) = M) ∧
    (∀ S T : Matrix (Phase n) (Phase n) ℝ,
      S ∈ Matrix.symplecticGroup (Fin n) ℝ →
      T ∈ Matrix.symplecticGroup (Fin n) ℝ →
      (S - 1).det ≠ 0 → (T - 1).det ≠ 0 → (S * T - 1).det ≠ 0 →
      (cayley S + cayley T).det ≠ 0 ∧
        cayley (S * T) = cayley S + (S.transpose - 1)⁻¹ * sigma n *
          (cayley S + cayley T)⁻¹ * sigma n * (S - 1)⁻¹ ∧
        (cayley S + cayley T)⁻¹ = -(T - 1) * (S * T - 1)⁻¹ * (S - 1) * sigma n) ∧
    (∀ S : Matrix (Phase n) (Phase n) ℝ,
      S ∈ Matrix.symplecticGroup (Fin n) ℝ → (S - 1).det ≠ 0 →
      (S⁻¹ - 1).det ≠ 0 ∧ cayley S⁻¹ = -cayley S) := by
  refine ⟨fun S hS hd => g64g_C.part1 S hS hd, fun M hM hd => ?_,
    fun S T hS _ hdS hdT hdST => g64g_C.part3 S T hS hdS hdT hdST,
    fun S hS hd => g64g_C.part4 S hS hd⟩
  obtain ⟨h1, h2, h3⟩ := g64g_C.part2 M hd
  exact ⟨h3.2 hM, h1, h2⟩
