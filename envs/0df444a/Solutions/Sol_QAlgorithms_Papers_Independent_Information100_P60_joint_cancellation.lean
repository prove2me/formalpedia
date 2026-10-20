-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Information100.P60.joint_cancellation
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-20T04:56:14.144084+00:00
-- url     : https://prove2.me/submissions/dc7addb1-724a-43b9-a7a2-ef6cf1eca8c4

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P60

open scoped Matrix ComplexConjugate

namespace G54J
lemma diagz {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (hA : A.IsHermitian) :
    ∃ U : Matrix (Fin n) (Fin n) ℂ, Uᴴ * U = 1 ∧ ∃ μ : Fin n → ℝ,
      Uᴴ * A * U = Matrix.diagonal (fun i => (μ i : ℂ)) ∧ (∑ i, (μ i : ℂ)) = A.trace := by
  obtain ⟨U, μ, h1, hs, ht⟩ : ∃ (U : Matrix (Fin n) (Fin n) ℂ) (μ : Fin n → ℝ), star U * U = 1 ∧
      A = U * Matrix.diagonal (fun i => (μ i : ℂ)) * star U ∧ (∑ i, (μ i : ℂ)) = A.trace := by
    refine ⟨(hA.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ), hA.eigenvalues,
      Unitary.star_mul_self_of_mem hA.eigenvectorUnitary.2, ?_, ?_⟩
    · have hs := hA.spectral_theorem
      rw [Unitary.conjStarAlgAut_apply] at hs
      exact hs
    · rw [hA.trace_eq_sum_eigenvalues]; rfl
  refine ⟨U, by rw [← Matrix.star_eq_conjTranspose]; exact h1, μ, ?_, ht⟩
  rw [hs, ← Matrix.star_eq_conjTranspose]
  simp only [← mul_assoc]
  rw [h1, one_mul, mul_assoc, h1, mul_one]

/-- 2×2 step: a common zero-diagonal unitary frame for two traceless Hermitian matrices. -/
lemma two {KA KB : Matrix (Fin 2) (Fin 2) ℂ} (hA : KA.IsHermitian) (hB : KB.IsHermitian)
    (tA : KA.trace = 0) (tB : KB.trace = 0) :
    ∃ G : Matrix (Fin 2) (Fin 2) ℂ, Gᴴ * G = 1 ∧ (∀ i, (Gᴴ * KA * G) i i = 0) ∧
      (∀ i, (Gᴴ * KB * G) i i = 0) := by
  obtain ⟨U, hU, μ, hμ, hμs⟩ := diagz KA hA
  set L := Uᴴ * KB * U with hL
  have hLH : L.IsHermitian := by
    rw [hL]; simpa [mul_assoc] using Matrix.isHermitian_conjTranspose_mul_mul U hB
  have hLt : L 0 0 + L 1 1 = 0 := by
    have : L.trace = KB.trace := by
      rw [hL, Matrix.trace_mul_cycle, mul_eq_one_comm.mp hU, one_mul]
    rw [tB, Matrix.trace_fin_two] at this; exact this
  have hL10 : L 1 0 = conj (L 0 1) := by
    have := congrFun (congrFun hLH 1) 0
    rw [Matrix.conjTranspose_apply] at this
    rw [← this]; rfl
  -- phase e with Re (e * L 0 1) = 0
  obtain ⟨e, he1, hre⟩ : ∃ e : ℂ, conj e * e = 1 ∧ e * L 0 1 + conj e * conj (L 0 1) = 0 := by
    by_cases h0 : L 0 1 = 0
    · exact ⟨1, by simp, by simp [h0]⟩
    · have hn : (‖L 0 1‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.mpr h0
      refine ⟨Complex.I * conj (L 0 1) / ‖L 0 1‖, ?_, ?_⟩
      · have hmul : conj (L 0 1) * L 0 1 = (‖L 0 1‖ : ℂ) ^ 2 := by
          rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]; push_cast; ring
        simp only [map_div₀, map_mul, Complex.conj_I, Complex.conj_conj, Complex.conj_ofReal]
        field_simp
        linear_combination hmul + (-(L 0 1 * conj (L 0 1))) * Complex.I_sq
      · have hmul : conj (L 0 1) * L 0 1 = (‖L 0 1‖ : ℂ) ^ 2 := by
          rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]; push_cast; ring
        simp only [map_div₀, map_mul, Complex.conj_I, Complex.conj_conj, Complex.conj_ofReal]
        field_simp
        ring
  set s : ℂ := (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) with hs
  have hs2 : s * s = 1 / 2 := by
    rw [hs, ← Complex.ofReal_mul, ← mul_inv, Real.mul_self_sqrt (by norm_num)]; push_cast; ring
  have hsc : conj s = s := by rw [hs, Complex.conj_ofReal]
  let H : Matrix (Fin 2) (Fin 2) ℂ := !![s, s; s * e, -(s * e)]
  have hH : Hᴴ * H = 1 := by
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [H, Matrix.mul_apply, Fin.sum_univ_two, hsc]
    · linear_combination 2 * hs2 + (s * s) * he1
    · linear_combination (-(s * s)) * he1
    · linear_combination (-(s * s)) * he1
    · linear_combination 2 * hs2 + (s * s) * he1
  refine ⟨U * H, ?_, ?_, ?_⟩
  · rw [Matrix.conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc Uᴴ, hU, Matrix.one_mul, hH]
  · have : (U * H)ᴴ * KA * (U * H) = Hᴴ * (Uᴴ * KA * U) * H := by
      simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    rw [this, hμ]
    have hμ0 : (μ 0 : ℂ) + μ 1 = 0 := by
      rw [Fin.sum_univ_two] at hμs; rw [hμs]; exact tA
    intro i; fin_cases i <;>
      simp [H, Matrix.mul_apply, Fin.sum_univ_two, hsc, Matrix.diagonal_apply]
    · linear_combination (s * s) * hμ0 + (s * s * μ 1) * he1
    · linear_combination (s * s) * hμ0 + (s * s * μ 1) * he1
  · have : (U * H)ᴴ * KB * (U * H) = Hᴴ * L * H := by
      simp only [hL, Matrix.conjTranspose_mul, Matrix.mul_assoc]
    rw [this]
    intro i; fin_cases i <;>
      simp [H, Matrix.mul_apply, Fin.sum_univ_two, hsc]
    · linear_combination (s * s) * hLt + (s * s) * hre + (s * s * conj e) * hL10 + (s * s * L 1 1) * he1
    · linear_combination (s * s) * hLt - (s * s) * hre - (s * s * conj e) * hL10 + (s * s * L 1 1) * he1

noncomputable def ω : ℂ := Complex.exp (2 * Real.pi * Complex.I / 3)

lemma ω_prim : IsPrimitiveRoot ω 3 := Complex.isPrimitiveRoot_exp 3 (by norm_num)
lemma ω3 : ω ^ 3 = 1 := ω_prim.pow_eq_one
lemma ωsum : 1 + ω + ω ^ 2 = 0 := by
  have := ω_prim.geom_sum_eq_zero (by norm_num : 1 < 3)
  simpa [Finset.sum_range_succ] using this
lemma ωnorm : ‖ω‖ = 1 := ω_prim.norm'_eq_one (by norm_num)
lemma ωconj : conj ω = ω ^ 2 := by
  have h : conj ω * ω = 1 := by
    rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq, ωnorm]; simp
  have : conj ω = conj ω * ω ^ 3 := by rw [ω3, mul_one]
  rw [this]; linear_combination (ω ^ 2) * h
lemma ωpow (n : ℕ) : ω ^ n = ω ^ (n % 3) := by
  conv_lhs => rw [← Nat.div_add_mod n 3, pow_add, pow_mul, ω3, one_pow, one_mul]

lemma w3 : ω ^ 3 = 1 := by rw [ωpow] <;> norm_num
lemma w4 : ω ^ 4 = ω := by rw [ωpow] <;> norm_num
lemma w5 : ω ^ 5 = ω ^ 2 := by rw [ωpow] <;> norm_num
lemma w6 : ω ^ 6 = 1 := by rw [ωpow] <;> norm_num
lemma w7 : ω ^ 7 = ω := by rw [ωpow] <;> norm_num
lemma w8 : ω ^ 8 = ω ^ 2 := by rw [ωpow] <;> norm_num
lemma w9 : ω ^ 9 = 1 := by rw [ωpow] <;> norm_num
lemma w10 : ω ^ 10 = ω := by rw [ωpow] <;> norm_num
lemma w11 : ω ^ 11 = ω ^ 2 := by rw [ωpow] <;> norm_num
lemma w12 : ω ^ 12 = 1 := by rw [ωpow] <;> norm_num

noncomputable def s3 : ℂ := (((Real.sqrt 3)⁻¹ : ℝ) : ℂ)
lemma s3sq : s3 * s3 = 1 / 3 := by
  rw [s3, ← Complex.ofReal_mul, ← mul_inv, Real.mul_self_sqrt (by norm_num)]; push_cast; ring
lemma s3conj : conj s3 = s3 := by rw [s3, Complex.conj_ofReal]

noncomputable def F : Matrix (Fin 3) (Fin 3) ℂ := Matrix.of fun j k => s3 * ω ^ (j.val * k.val)

lemma F_unitary : Fᴴ * F = 1 := by
  ext j k
  fin_cases j <;> fin_cases k <;>
    simp [F, Matrix.mul_apply, Fin.sum_univ_three, s3conj, ωconj, ← pow_mul, Matrix.one_apply] <;>
    simp only [← pow_add, ← mul_assoc, mul_comm _ s3] <;> norm_num <;>
    ring_nf <;> (try simp only [w3, w4, w5, w6, w7, w8, w9, w10, w11, w12]) <;> (try ring_nf) <;>
    first
    | linear_combination (3 : ℂ) * s3sq
    | linear_combination (s3 ^ 2) * ωsum


lemma ivt3 (f : ℝ → ℝ) (hf : Continuous f) (a b c : ℝ) (h : f a + f b + f c = 0) :
    ∃ t, f t = 0 := by
  have key : ∀ x y : ℝ, (min (f x) (f y) ≤ 0 ∧ 0 ≤ max (f x) (f y)) → ∃ t, f t = 0 := by
    intro x y hxy
    have hm : (0 : ℝ) ∈ Set.uIcc (f x) (f y) := by
      rw [Set.uIcc, Set.mem_Icc]; exact hxy
    obtain ⟨t, -, ht⟩ := intermediate_value_uIcc hf.continuousOn hm
    exact ⟨t, ht⟩
  by_cases h1 : min (f a) (f b) ≤ 0 ∧ 0 ≤ max (f a) (f b)
  · exact key a b h1
  · apply key b c
    rw [not_and_or, not_le, not_le] at h1
    rcases h1 with h1 | h1
    · have ha : 0 < f a := lt_of_lt_of_le h1 (min_le_left _ _)
      have hb : 0 < f b := lt_of_lt_of_le h1 (min_le_right _ _)
      exact ⟨min_le_of_right_le (by linarith), le_max_of_le_left hb.le⟩
    · have ha : f a < 0 := lt_of_le_of_lt (le_max_left _ _) h1
      have hb : f b < 0 := lt_of_le_of_lt (le_max_right _ _) h1
      exact ⟨min_le_of_left_le hb.le, le_max_of_le_right (by linarith)⟩

noncomputable def dvec (t : ℝ) : Fin 3 → ℂ := fun k => Complex.exp (((k.val : ℝ) * t : ℝ) * Complex.I)

noncomputable def Vt (t : ℝ) : Matrix (Fin 3) (Fin 3) ℂ := Matrix.diagonal (dvec t) * F

lemma dvec_unit (t : ℝ) (k : Fin 3) : conj (dvec t k) * dvec t k = 1 := by
  rw [dvec, ← Complex.exp_conj, ← Complex.exp_add]
  simp [Complex.conj_ofReal]

lemma D_unitary (t : ℝ) : (Matrix.diagonal (dvec t))ᴴ * Matrix.diagonal (dvec t) = 1 := by
  rw [Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1; funext k; exact dvec_unit t k

lemma Vt_unitary (t : ℝ) : (Vt t)ᴴ * Vt t = 1 := by
  rw [Vt, Matrix.conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc _ (Matrix.diagonal _),
    D_unitary, Matrix.one_mul, F_unitary]

lemma col_eq {X Y B : Matrix (Fin 3) (Fin 3) ℂ} {m : Fin 3} (h : ∀ j, X j 0 = Y j m) :
    (Xᴴ * B * X) 0 0 = (Yᴴ * B * Y) m m := by
  simp [Matrix.mul_apply, Matrix.conjTranspose_apply, h]

lemma Vt_col (m : Fin 3) (j : Fin 3) : Vt (2 * Real.pi * m.val / 3) j 0 = F j m := by
  simp only [Vt, F, Matrix.diagonal_mul, Matrix.of_apply, dvec, Fin.val_zero, mul_zero, pow_zero,
    mul_one]
  rw [mul_comm, ω, ← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

lemma first_vec (lam : Fin 3 → ℂ) (hl : ∑ i, lam i = 0) (B : Matrix (Fin 3) (Fin 3) ℂ)
    (hB : B.IsHermitian) (tB : B.trace = 0) :
    ∃ V : Matrix (Fin 3) (Fin 3) ℂ, Vᴴ * V = 1 ∧ (Vᴴ * Matrix.diagonal lam * V) 0 0 = 0 ∧
      (Vᴴ * B * V) 0 0 = 0 := by
  let f : ℝ → ℝ := fun t => (((Vt t)ᴴ * B * Vt t) 0 0).re
  have hfc : Continuous f := by
    have : Continuous Vt := by
      unfold Vt dvec
      fun_prop
    fun_prop
  have hsum : f (2 * Real.pi * (0 : Fin 3).val / 3) + f (2 * Real.pi * (1 : Fin 3).val / 3) +
      f (2 * Real.pi * (2 : Fin 3).val / 3) = 0 := by
    simp only [f]
    rw [col_eq (Vt_col 0), col_eq (Vt_col 1), col_eq (Vt_col 2)]
    have htr : (Fᴴ * B * F).trace = 0 := by
      rw [Matrix.trace_mul_cycle, mul_eq_one_comm.mp F_unitary, Matrix.one_mul, tB]
    rw [Matrix.trace, Fin.sum_univ_three] at htr
    have := congrArg Complex.re htr
    simpa using this
  obtain ⟨t, ht⟩ := ivt3 f hfc _ _ _ hsum
  refine ⟨Vt t, Vt_unitary t, ?_, ?_⟩
  · have hc : (Matrix.diagonal (dvec t))ᴴ * Matrix.diagonal lam * Matrix.diagonal (dvec t) =
        Matrix.diagonal lam := by
      rw [Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
      congr 1; funext k
      rw [show star (dvec t) k * lam k * dvec t k = lam k * (conj (dvec t k) * dvec t k) by
        simp only [Pi.star_apply]; rw [Complex.star_def]; ring, dvec_unit, mul_one]
    have : (Vt t)ᴴ * Matrix.diagonal lam * Vt t = Fᴴ * Matrix.diagonal lam * F := by
      rw [Vt, Matrix.conjTranspose_mul]
      rw [show Fᴴ * (Matrix.diagonal (dvec t))ᴴ * Matrix.diagonal lam * (Matrix.diagonal (dvec t) * F)
        = Fᴴ * ((Matrix.diagonal (dvec t))ᴴ * Matrix.diagonal lam * Matrix.diagonal (dvec t)) * F by
        simp only [Matrix.mul_assoc], hc]
    rw [this]
    simp only [F, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply, Matrix.diagonal_apply,
      Fin.sum_univ_three] at hl ⊢
    simp [s3conj]
    linear_combination (s3 * s3) * hl
  · have hH : ((Vt t)ᴴ * B * Vt t).IsHermitian := by
      simpa [Matrix.mul_assoc] using Matrix.isHermitian_conjTranspose_mul_mul (Vt t) hB
    apply Complex.ext
    · simpa [f] using ht
    · have := congrFun (congrFun hH 0) 0
      rw [Matrix.conjTranspose_apply] at this
      have h2 := congrArg Complex.im this
      simp at h2
      simp; linarith

noncomputable def blk (G2 : Matrix (Fin 2) (Fin 2) ℂ) : Matrix (Fin 3) (Fin 3) ℂ :=
  !![1, 0, 0; 0, G2 0 0, G2 0 1; 0, G2 1 0, G2 1 1]

lemma blk_unitary {G2 : Matrix (Fin 2) (Fin 2) ℂ} (h : G2ᴴ * G2 = 1) : (blk G2)ᴴ * blk G2 = 1 := by
  have e : ∀ i j, (G2ᴴ * G2) i j = (1 : Matrix (Fin 2) (Fin 2) ℂ) i j := fun i j => by rw [h]
  have e00 := e 0 0; have e01 := e 0 1; have e10 := e 1 0; have e11 := e 1 1
  simp [Matrix.mul_apply, Fin.sum_univ_two] at e00 e01 e10 e11
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [blk, Matrix.mul_apply, Fin.sum_univ_three, Matrix.one_apply] <;> assumption

lemma blk_conj00 (G2 : Matrix (Fin 2) (Fin 2) ℂ) (X : Matrix (Fin 3) (Fin 3) ℂ) :
    ((blk G2)ᴴ * X * blk G2) 0 0 = X 0 0 := by
  simp [blk, Matrix.mul_apply, Fin.sum_univ_three]

lemma blk_conjs (G2 : Matrix (Fin 2) (Fin 2) ℂ) (X : Matrix (Fin 3) (Fin 3) ℂ) (a : Fin 2) :
    ((blk G2)ᴴ * X * blk G2) a.succ a.succ = (G2ᴴ * X.submatrix Fin.succ Fin.succ * G2) a a := by
  fin_cases a <;> simp [blk, Matrix.mul_apply, Fin.sum_univ_three, Fin.sum_univ_two] <;> ring

lemma herm_conj {n : ℕ} {X : Matrix (Fin n) (Fin n) ℂ} (V : Matrix (Fin n) (Fin n) ℂ)
    (hX : X.IsHermitian) : (Vᴴ * X * V).IsHermitian := by
  simpa [Matrix.mul_assoc] using Matrix.isHermitian_conjTranspose_mul_mul V hX

lemma trace_conj {n : ℕ} {X V : Matrix (Fin n) (Fin n) ℂ} (hV : Vᴴ * V = 1) :
    (Vᴴ * X * V).trace = X.trace := by
  rw [Matrix.trace_mul_cycle, mul_eq_one_comm.mp hV, Matrix.one_mul]

lemma zero_diag (A B : Matrix (Fin 3) (Fin 3) ℂ) (hA : A.IsHermitian) (hB : B.IsHermitian)
    (tA : A.trace = 0) (tB : B.trace = 0) :
    ∃ V : Matrix (Fin 3) (Fin 3) ℂ, Vᴴ * V = 1 ∧ ∀ i, (Vᴴ * A * V) i i = 0 ∧ (Vᴴ * B * V) i i = 0 := by
  obtain ⟨U, hU, μ, hμ, hμs⟩ := diagz A hA
  obtain ⟨V', hV', h0A, h0B⟩ := first_vec (fun i => (μ i : ℂ)) (by rw [hμs, tA]) (Uᴴ * B * U)
    (herm_conj U hB) (by rw [trace_conj hU, tB])
  set V1 := U * V' with hV1
  have hV1u : V1ᴴ * V1 = 1 := by
    rw [hV1, Matrix.conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc Uᴴ, hU, Matrix.one_mul, hV']
  have hc : ∀ X : Matrix (Fin 3) (Fin 3) ℂ, V1ᴴ * X * V1 = V'ᴴ * (Uᴴ * X * U) * V' := by
    intro X; simp only [hV1, Matrix.conjTranspose_mul, Matrix.mul_assoc]
  set A1 := V1ᴴ * A * V1 with hA1
  set B1 := V1ᴴ * B * V1 with hB1
  have a00 : A1 0 0 = 0 := by rw [hA1, hc, hμ]; exact h0A
  have b00 : B1 0 0 = 0 := by rw [hB1, hc]; exact h0B
  have tsub : ∀ X : Matrix (Fin 3) (Fin 3) ℂ, X.trace = 0 → X 0 0 = 0 →
      (X.submatrix Fin.succ Fin.succ).trace = 0 := by
    intro X hX h0
    rw [Matrix.trace, Fin.sum_univ_succ] at hX
    rw [Matrix.trace]
    simpa [h0] using hX
  obtain ⟨G2, hG2, hGA, hGB⟩ := two ((herm_conj V1 hA).submatrix Fin.succ)
    ((herm_conj V1 hB).submatrix Fin.succ) (tsub A1 (by rw [hA1, trace_conj hV1u, tA]) a00)
    (tsub B1 (by rw [hB1, trace_conj hV1u, tB]) b00)
  refine ⟨V1 * blk G2, ?_, ?_⟩
  · rw [Matrix.conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc V1ᴴ, hV1u, Matrix.one_mul,
      blk_unitary hG2]
  · have hc2 : ∀ X : Matrix (Fin 3) (Fin 3) ℂ, (V1 * blk G2)ᴴ * X * (V1 * blk G2) =
        (blk G2)ᴴ * (V1ᴴ * X * V1) * blk G2 := by
      intro X; simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    intro i
    rw [hc2, hc2]
    refine Fin.cases ?_ (fun a => ?_) i
    · rw [blk_conj00, blk_conj00]; exact ⟨a00, b00⟩
    · rw [blk_conjs, blk_conjs]; exact ⟨hGA a, hGB a⟩

noncomputable def dω : Fin 3 → ℂ := ![1, ω, ω ^ 2]

lemma dω_unit (k : Fin 3) : conj (dω k) * dω k = 1 := by
  have h : conj ω * ω = 1 := by
    rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq, ωnorm]; simp
  fin_cases k <;> simp [dω]
  · exact h
  · rw [← mul_pow, h, one_pow]

lemma dω_off (j k : Fin 3) (hjk : j ≠ k) : 1 + dω j * conj (dω k) + conj (dω j) * dω k = 0 := by
  fin_cases j <;> fin_cases k <;> simp [dω, ωconj] at hjk ⊢ <;> ring_nf <;>
    (try simp only [w3, w4, w5, w6, w7, w8]) <;> (try ring_nf) <;> linear_combination ωsum

lemma inner_zero (M' : Matrix (Fin 3) (Fin 3) ℂ) (h : ∀ i, M' i i = 0) :
    M' + Matrix.diagonal dω * M' * (Matrix.diagonal dω)ᴴ +
      (Matrix.diagonal dω)ᴴ * M' * Matrix.diagonal dω = 0 := by
  ext j k
  rw [Matrix.diagonal_conjTranspose]
  simp only [Matrix.add_apply, Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.zero_apply,
    Pi.star_apply, Complex.star_def]
  by_cases hjk : j = k
  · subst hjk; rw [h]; ring
  · linear_combination (M' j k) * dω_off j k hjk

lemma final_eq (V M : Matrix (Fin 3) (Fin 3) ℂ) (hV : Vᴴ * V = 1) (h : ∀ i, (Vᴴ * M * V) i i = 0) :
    M + (V * Matrix.diagonal dω * Vᴴ) * M * (V * Matrix.diagonal dω * Vᴴ)ᴴ +
      (V * Matrix.diagonal dω * Vᴴ)ᴴ * M * (V * Matrix.diagonal dω * Vᴴ) = 0 := by
  have hV' : V * Vᴴ = 1 := mul_eq_one_comm.mp hV
  have hM : M = V * (Vᴴ * M * V) * Vᴴ := by
    simp only [← Matrix.mul_assoc]; rw [hV', Matrix.one_mul, Matrix.mul_assoc, hV', Matrix.mul_one]
  have key := inner_zero (Vᴴ * M * V) h
  have : M + (V * Matrix.diagonal dω * Vᴴ) * M * (V * Matrix.diagonal dω * Vᴴ)ᴴ +
      (V * Matrix.diagonal dω * Vᴴ)ᴴ * M * (V * Matrix.diagonal dω * Vᴴ) =
      V * ((Vᴴ * M * V) + Matrix.diagonal dω * (Vᴴ * M * V) * (Matrix.diagonal dω)ᴴ +
      (Matrix.diagonal dω)ᴴ * (Vᴴ * M * V) * Matrix.diagonal dω) * Vᴴ := by
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
    simp only [Matrix.mul_assoc]
    simp only [← Matrix.mul_assoc V Vᴴ, hV', Matrix.one_mul, Matrix.mul_one]
  rw [this, key, Matrix.mul_zero, Matrix.zero_mul]

lemma W_unitary (V : Matrix (Fin 3) (Fin 3) ℂ) (hV : Vᴴ * V = 1) :
    (V * Matrix.diagonal dω * Vᴴ)ᴴ * (V * Matrix.diagonal dω * Vᴴ) = 1 := by
  have hV' : V * Vᴴ = 1 := mul_eq_one_comm.mp hV
  have hD : (Matrix.diagonal dω)ᴴ * Matrix.diagonal dω = 1 := by
    rw [Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1; funext k; exact dω_unit k
  simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
  simp only [← Matrix.mul_assoc Vᴴ V, hV, Matrix.one_mul]
  simp only [← Matrix.mul_assoc (Matrix.diagonal dω)ᴴ, hD, Matrix.one_mul, hV']

end G54J

open scoped Matrix ComplexConjugate ENNReal
open Filter Topology
open QAlgorithms.Papers.Independent.Information100.P60

theorem solution (A B : Mat (Fin 3)) (hA : A.IsHermitian) (hB : B.IsHermitian)
    (htA : A.trace = 0) (htB : B.trace = 0) :
    ∃ W : Matrix.unitaryGroup (Fin 3) ℂ, ∀ M ∈ ({A, B} : Set (Mat (Fin 3))),
      M + (W : Mat (Fin 3)) * M * (W : Mat (Fin 3))ᴴ + (W : Mat (Fin 3))ᴴ * M * (W : Mat (Fin 3)) = 0 := by
  obtain ⟨V, hV, hz⟩ := G54J.zero_diag A B hA hB htA htB
  refine ⟨⟨V * Matrix.diagonal G54J.dω * Vᴴ, ?_⟩, ?_⟩
  · rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose]
    exact G54J.W_unitary V hV
  · intro M hM
    rcases hM with rfl | hM
    · exact G54J.final_eq V M hV (fun i => (hz i).1)
    · rw [Set.mem_singleton_iff] at hM; subst hM
      exact G54J.final_eq V M hV (fun i => (hz i).2)
