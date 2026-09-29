-- Prove2me | solution 1 for THDM.thm4_gauge_orbits
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T08:49:33.034901+00:00
-- url     : https://prove2.me/submissions/19668510-c255-4711-a992-ba4aaf38c29c

import Definitions.Def_THDM_stationary

open scoped BigOperators ComplexConjugate
open Matrix
open THDM

theorem W7b_THDM_K_apply (φ : HiggsMat) (i j : Fin 2) :
    Kmat φ i j = φ i 0 * conj (φ j 0) + φ i 1 * conj (φ j 1) := by
  rw [Kmat, Matrix.mul_apply, Fin.sum_univ_two]
  simp [Matrix.conjTranspose_apply, Complex.star_def]

theorem W7b_THDM_mul_conj (z : ℂ) : z * conj z = (Complex.normSq z : ℂ) := Complex.mul_conj z

/-- The matrix whose rows are `(p, q)` and `(-q̄, p̄)`. -/
def W7b_THDM_M (X : HiggsMat) : HiggsMat :=
  !![X 0 0, X 0 1; -conj (X 0 1), conj (X 0 0)]

theorem W7b_THDM_mul_M (X : HiggsMat) :
    X * (W7b_THDM_M X)ᴴ = !![Kmat X 0 0, 0; Kmat X 1 0, X.det] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    (rw [Matrix.mul_apply, Fin.sum_univ_two]
     simp [W7b_THDM_M, Matrix.conjTranspose_apply, Complex.star_def, W7b_THDM_K_apply,
       Matrix.det_fin_two]
     try ring)

theorem W7b_THDM_M_M (X : HiggsMat) : W7b_THDM_M (W7b_THDM_M X) = W7b_THDM_M X := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [W7b_THDM_M]

theorem W7b_THDM_M_unitary_aux (X : HiggsMat) :
    W7b_THDM_M X * (W7b_THDM_M X)ᴴ =
      ((Complex.normSq (X 0 0) + Complex.normSq (X 0 1) : ℝ) : ℂ) • 1 := by
  have h := W7b_THDM_mul_M (W7b_THDM_M X)
  rw [W7b_THDM_M_M] at h
  rw [h]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [W7b_THDM_K_apply, W7b_THDM_M, Matrix.det_fin_two, W7b_THDM_mul_conj] <;> ring

/-- The unitary matrix built from the first row of `X`. -/
noncomputable def W7b_THDM_W (X : HiggsMat) : HiggsMat :=
  ((Real.sqrt (Complex.normSq (X 0 0) + Complex.normSq (X 0 1)) : ℝ) : ℂ)⁻¹ • W7b_THDM_M X

theorem W7b_THDM_W_unitary (X : HiggsMat) (h : 0 < Complex.normSq (X 0 0) + Complex.normSq (X 0 1)) :
    W7b_THDM_W X * (W7b_THDM_W X)ᴴ = 1 ∧ (W7b_THDM_W X)ᴴ * W7b_THDM_W X = 1 := by
  set n := Real.sqrt (Complex.normSq (X 0 0) + Complex.normSq (X 0 1)) with hn
  have hn0 : 0 < n := Real.sqrt_pos.mpr h
  have hn2 : n ^ 2 = Complex.normSq (X 0 0) + Complex.normSq (X 0 1) := Real.sq_sqrt h.le
  have h1 : W7b_THDM_W X * (W7b_THDM_W X)ᴴ = 1 := by
    unfold W7b_THDM_W
    rw [← hn, Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
      W7b_THDM_M_unitary_aux, smul_smul, ← hn2]
    have hnc : (n : ℂ) ≠ 0 := by exact_mod_cast hn0.ne'
    have : (n : ℂ)⁻¹ * star ((n : ℂ)⁻¹) * ((n ^ 2 : ℝ) : ℂ) = 1 := by
      rw [star_inv₀, Complex.star_def, Complex.conj_ofReal]
      push_cast; field_simp
    rw [this, one_smul]
  exact ⟨h1, mul_eq_one_comm.mp h1⟩

theorem W7b_THDM_det_K (φ : HiggsMat) : (Kmat φ).det = (Complex.normSq φ.det : ℂ) := by
  rw [Kmat, Matrix.det_mul, Matrix.det_conjTranspose, Complex.star_def]
  exact Complex.mul_conj _

theorem W7b_THDM_K00 (φ : HiggsMat) :
    Kmat φ 0 0 = ((Complex.normSq (φ 0 0) + Complex.normSq (φ 0 1) : ℝ) : ℂ) := by
  rw [W7b_THDM_K_apply, W7b_THDM_mul_conj, W7b_THDM_mul_conj]; push_cast; ring

/-- Main step: if the first row of `φ` is nonzero, equal `K` gives `ψ = φ V` with `V` unitary. -/
theorem W7b_THDM_main (φ ψ : HiggsMat) (hK : Kmat φ = Kmat ψ)
    (h : 0 < Complex.normSq (φ 0 0) + Complex.normSq (φ 0 1)) :
    ∃ V : Matrix (Fin 2) (Fin 2) ℂ, V * Vᴴ = 1 ∧ ψ = φ * V := by
  have e00 := congrFun (congrFun hK 0) 0
  have e10 := congrFun (congrFun hK 1) 0
  have hn : Complex.normSq (φ 0 0) + Complex.normSq (φ 0 1) =
      Complex.normSq (ψ 0 0) + Complex.normSq (ψ 0 1) := by
    rw [W7b_THDM_K00, W7b_THDM_K00] at e00; exact_mod_cast e00
  have h' : 0 < Complex.normSq (ψ 0 0) + Complex.normSq (ψ 0 1) := hn ▸ h
  obtain ⟨Wφ1, Wφ2⟩ := W7b_THDM_W_unitary φ h
  obtain ⟨Wψ1, Wψ2⟩ := W7b_THDM_W_unitary ψ h'
  have hdd : Complex.normSq ψ.det = Complex.normSq φ.det := by
    have := congrArg Matrix.det hK
    rw [W7b_THDM_det_K, W7b_THDM_det_K] at this
    exact_mod_cast this.symm
  obtain ⟨lam, hlam1, hlam2⟩ : ∃ lam : ℂ, Complex.normSq lam = 1 ∧ lam * φ.det = ψ.det := by
    by_cases h0 : φ.det = 0
    · refine ⟨1, by simp, ?_⟩
      rw [h0, Complex.normSq_zero] at hdd
      rw [Complex.normSq_eq_zero.mp hdd, h0, mul_zero]
    · refine ⟨ψ.det / φ.det, ?_, by field_simp⟩
      rw [Complex.normSq_div, hdd, div_self]
      exact (Complex.normSq_pos.mpr h0).ne'
  set D : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, lam] with hD
  have hDu : D * Dᴴ = 1 := by
    have : lam * conj lam = 1 := by rw [W7b_THDM_mul_conj, hlam1]; simp
    ext i j
    fin_cases i <;> fin_cases j <;>
      (rw [Matrix.mul_apply, Fin.sum_univ_two]
       simp [hD, Matrix.conjTranspose_apply, Complex.star_def, this])
  set Wφ := W7b_THDM_W φ
  set Wψ := W7b_THDM_W ψ
  have hkey : ψ * Wψᴴ = φ * Wφᴴ * D := by
    have hnn : Real.sqrt (Complex.normSq (ψ 0 0) + Complex.normSq (ψ 0 1)) =
        Real.sqrt (Complex.normSq (φ 0 0) + Complex.normSq (φ 0 1)) := by rw [hn]
    simp only [Wψ, Wφ, W7b_THDM_W, hnn, Matrix.conjTranspose_smul, Matrix.mul_smul,
      Matrix.smul_mul, W7b_THDM_mul_M]
    congr 1
    rw [← e00, ← e10, ← hlam2]
    ext i j
    fin_cases i <;> fin_cases j <;>
      (rw [Matrix.mul_apply, Fin.sum_univ_two]
       simp [hD]
       try ring)
  refine ⟨Wφᴴ * D * Wψ, ?_, ?_⟩
  · calc Wφᴴ * D * Wψ * (Wφᴴ * D * Wψ)ᴴ
        = Wφᴴ * D * (Wψ * Wψᴴ) * Dᴴ * Wφ := by
          simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
      _ = Wφᴴ * Wφ := by rw [Wψ1, Matrix.mul_one, Matrix.mul_assoc Wφᴴ, hDu, Matrix.mul_one]
      _ = 1 := Wφ2
  · calc ψ = ψ * (Wψᴴ * Wψ) := by rw [Wψ2, Matrix.mul_one]
      _ = (ψ * Wψᴴ) * Wψ := by rw [Matrix.mul_assoc]
      _ = φ * (Wφᴴ * D * Wψ) := by rw [hkey]; simp only [Matrix.mul_assoc]

theorem W7b_THDM_part1 (φ ψ : HiggsMat) (hK : Kmat φ = Kmat ψ) : GaugeEquiv φ ψ := by
  have toU : (∃ V : Matrix (Fin 2) (Fin 2) ℂ, V * Vᴴ = 1 ∧ ψ = φ * V) → GaugeEquiv φ ψ := by
    rintro ⟨V, hV, hψ⟩
    refine ⟨Vᵀ, ?_, by rw [Matrix.transpose_transpose]; exact hψ⟩
    have : (V * Vᴴ)ᵀ = 1 := by rw [hV, Matrix.transpose_one]
    rw [Matrix.transpose_mul] at this
    rw [← this]
    rfl
  apply toU
  by_cases h1 : 0 < Complex.normSq (φ 0 0) + Complex.normSq (φ 0 1)
  · exact W7b_THDM_main φ ψ hK h1
  · -- first row of `φ` vanishes; swap the rows
    set σ : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 1, 0] with hσ
    have hσσ : σ * σ = 1 := by
      ext i j; fin_cases i <;> fin_cases j <;>
        (rw [Matrix.mul_apply, Fin.sum_univ_two]; simp [hσ])
    have hKs : Kmat (σ * φ) = Kmat (σ * ψ) := by
      simp only [Kmat, Matrix.conjTranspose_mul, Matrix.mul_assoc]
      rw [← Matrix.mul_assoc φ, ← Matrix.mul_assoc ψ]
      rw [show φ * φᴴ = Kmat φ from rfl, show ψ * ψᴴ = Kmat ψ from rfl, hK]
    have hs0 : ∀ X : HiggsMat, (σ * X) 0 0 = X 1 0 ∧ (σ * X) 0 1 = X 1 1 := by
      intro X; constructor <;> (rw [Matrix.mul_apply, Fin.sum_univ_two]; simp [hσ])
    by_cases h2 : 0 < Complex.normSq (φ 1 0) + Complex.normSq (φ 1 1)
    · have h2' : 0 < Complex.normSq ((σ * φ) 0 0) + Complex.normSq ((σ * φ) 0 1) := by
        rw [(hs0 φ).1, (hs0 φ).2]; exact h2
      obtain ⟨V, hV, hψ⟩ := W7b_THDM_main (σ * φ) (σ * ψ) hKs h2'
      refine ⟨V, hV, ?_⟩
      calc ψ = σ * (σ * ψ) := by rw [← Matrix.mul_assoc, hσσ, Matrix.one_mul]
        _ = φ * V := by rw [hψ, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hσσ, Matrix.one_mul]
    · -- `φ = 0`, hence `ψ = 0`
      have n1 := Complex.normSq_nonneg (φ 0 0)
      have n2 := Complex.normSq_nonneg (φ 0 1)
      have n3 := Complex.normSq_nonneg (φ 1 0)
      have n4 := Complex.normSq_nonneg (φ 1 1)
      push_neg at h1 h2
      have hφ0 : φ = 0 := by
        ext i j
        fin_cases i <;> fin_cases j <;> simp <;> apply Complex.normSq_eq_zero.mp <;> linarith
      have e00 := congrFun (congrFun hK 0) 0
      have e11 := congrFun (congrFun hK 1) 1
      rw [W7b_THDM_K_apply, W7b_THDM_K_apply, hφ0] at e00 e11
      simp only [Matrix.zero_apply, zero_mul, add_zero, W7b_THDM_mul_conj] at e00 e11
      have a1 : Complex.normSq (ψ 0 0) + Complex.normSq (ψ 0 1) = 0 := by exact_mod_cast e00.symm
      have a2 : Complex.normSq (ψ 1 0) + Complex.normSq (ψ 1 1) = 0 := by exact_mod_cast e11.symm
      have m1 := Complex.normSq_nonneg (ψ 0 0)
      have m2 := Complex.normSq_nonneg (ψ 0 1)
      have m3 := Complex.normSq_nonneg (ψ 1 0)
      have m4 := Complex.normSq_nonneg (ψ 1 1)
      have hψ0 : ψ = 0 := by
        ext i j
        fin_cases i <;> fin_cases j <;> simp <;> apply Complex.normSq_eq_zero.mp <;> linarith
      exact ⟨1, by simp, by rw [hφ0, hψ0]; simp⟩

theorem W7b_THDM_K0_eq (φ : HiggsMat) : K0 φ =
    Complex.normSq (φ 0 0) + Complex.normSq (φ 0 1) + Complex.normSq (φ 1 0) + Complex.normSq (φ 1 1) := by
  unfold K0
  rw [Matrix.trace_fin_two, W7b_THDM_K_apply, W7b_THDM_K_apply]
  simp only [W7b_THDM_mul_conj]
  simp only [Complex.add_re, Complex.ofReal_re]
  ring

theorem W7b_THDM_Kvec_eq (φ : HiggsMat) (a : Fin 3) : Kvec φ a =
    ![2 * (Kmat φ 0 1).re, -2 * (Kmat φ 0 1).im, (Kmat φ 0 0).re - (Kmat φ 1 1).re] a := by
  have h10 : Kmat φ 1 0 = conj (Kmat φ 0 1) := by
    rw [W7b_THDM_K_apply, W7b_THDM_K_apply]; simp; ring
  unfold Kvec
  fin_cases a <;>
    simp [pauli, Matrix.trace_fin_two, Matrix.mul_apply, Fin.sum_univ_two, h10] <;> ring

theorem W7b_THDM_part2 (φ : HiggsMat) : (K0 φ, Kvec φ) ∈ forwardCone := by
  refine ⟨?_, ?_⟩
  · rw [W7b_THDM_K0_eq]
    have := Complex.normSq_nonneg (φ 0 0); have := Complex.normSq_nonneg (φ 0 1)
    have := Complex.normSq_nonneg (φ 1 0); have := Complex.normSq_nonneg (φ 1 1)
    linarith
  · simp only [dot3, Fin.sum_univ_three, W7b_THDM_Kvec_eq]
    rw [W7b_THDM_K0_eq]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
      Matrix.tail_cons]
    rw [W7b_THDM_K_apply, W7b_THDM_K_apply, W7b_THDM_K_apply]
    simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.mul_re,
      Complex.mul_im, Complex.conj_re, Complex.conj_im]
    nlinarith [sq_nonneg ((φ 0 0).re * (φ 1 1).re - (φ 0 0).im * (φ 1 1).im
        - (φ 0 1).re * (φ 1 0).re + (φ 0 1).im * (φ 1 0).im),
      sq_nonneg ((φ 0 0).re * (φ 1 1).im + (φ 0 0).im * (φ 1 1).re
        - (φ 0 1).re * (φ 1 0).im - (φ 0 1).im * (φ 1 0).re)]

theorem W7b_THDM_part3 (p : ℝ × (Fin 3 → ℝ)) (hp : p ∈ forwardCone) :
    ∃ φ : HiggsMat, K0 φ = p.1 ∧ Kvec φ = p.2 := by
  obtain ⟨k0, k⟩ := p
  obtain ⟨h0, hc⟩ := hp
  simp only [dot3, Fin.sum_univ_three] at hc h0
  have hK : ∀ φ : HiggsMat, Kvec φ = k ↔
      2 * (Kmat φ 0 1).re = k 0 ∧ -2 * (Kmat φ 0 1).im = k 1 ∧
        (Kmat φ 0 0).re - (Kmat φ 1 1).re = k 2 := by
    intro φ
    constructor
    · intro h
      refine ⟨?_, ?_, ?_⟩
      · have := congrFun h 0; rw [W7b_THDM_Kvec_eq] at this; simpa using this
      · have := congrFun h 1; rw [W7b_THDM_Kvec_eq] at this; simpa using this
      · have := congrFun h 2; rw [W7b_THDM_Kvec_eq] at this; simpa using this
    · rintro ⟨a1, a2, a3⟩
      funext a; rw [W7b_THDM_Kvec_eq]; fin_cases a <;> simp [a1, a2, a3]
  by_cases hpos : 0 < k0 + k 2
  · set α := Real.sqrt ((k0 + k 2) / 2) with hα
    have hα0 : 0 < α := Real.sqrt_pos.mpr (by linarith)
    have hα2 : α ^ 2 = (k0 + k 2) / 2 := Real.sq_sqrt (by linarith)
    set X := (k 0 ^ 2 + k 1 ^ 2) / (4 * α ^ 2) with hX
    set rad := (k0 - k 2) / 2 - X with hrad
    have hrad0 : 0 ≤ rad := by
      rw [hrad, hX, hα2]
      rw [show (k0 - k 2) / 2 - (k 0 ^ 2 + k 1 ^ 2) / (4 * ((k0 + k 2) / 2)) =
        ((k0 - k 2) * (k0 + k 2) - (k 0 ^ 2 + k 1 ^ 2)) / (2 * (k0 + k 2)) by field_simp; ring]
      apply div_nonneg _ (by linarith)
      nlinarith
    set γ := Real.sqrt rad with hγ
    have hγ2 : γ ^ 2 = rad := Real.sq_sqrt hrad0
    set β : ℂ := ((k 0 : ℂ) + Complex.I * (k 1 : ℂ)) / (2 * (α : ℂ)) with hβ
    have hαc : (α : ℂ) ≠ 0 := by exact_mod_cast hα0.ne'
    have hβn : Complex.normSq β = X := by
      rw [hβ, Complex.normSq_div, mul_comm Complex.I, Complex.normSq_add_mul_I,
        Complex.normSq_mul, Complex.normSq_ofReal, hX]
      simp [Complex.normSq_ofNat]
      field_simp; ring
    have hαβ : (α : ℂ) * conj β = ((k 0 : ℂ) - Complex.I * (k 1 : ℂ)) / 2 := by
      rw [hβ, map_div₀, map_add, map_mul, map_mul, Complex.conj_ofReal, Complex.conj_ofReal,
        Complex.conj_I, map_ofNat, Complex.conj_ofReal]
      field_simp; ring
    set φ : HiggsMat := !![(α : ℂ), 0; β, (γ : ℂ)] with hφ
    have k00 : Kmat φ 0 0 = ((α ^ 2 : ℝ) : ℂ) := by
      rw [W7b_THDM_K_apply]; simp [hφ]; push_cast; ring
    have k01 : Kmat φ 0 1 = ((k 0 : ℂ) - Complex.I * (k 1 : ℂ)) / 2 := by
      rw [W7b_THDM_K_apply]; simp [hφ, hαβ]
    have k11 : Kmat φ 1 1 = ((X + γ ^ 2 : ℝ) : ℂ) := by
      rw [W7b_THDM_K_apply]; simp [hφ, W7b_THDM_mul_conj, hβn]; push_cast; ring
    have k00re : (Kmat φ 0 0).re = α ^ 2 := by rw [k00, Complex.ofReal_re]
    have k11re : (Kmat φ 1 1).re = X + γ ^ 2 := by rw [k11, Complex.ofReal_re]
    have k01re : (Kmat φ 0 1).re = k 0 / 2 := by rw [k01]; simp
    have k01im : (Kmat φ 0 1).im = -(k 1) / 2 := by rw [k01]; simp <;> ring
    refine ⟨φ, ?_, ?_⟩
    · rw [W7b_THDM_K0_eq]
      simp [hφ, hβn, Complex.normSq_ofReal]
      linear_combination hα2 + hγ2 + hrad
    · rw [hK, k00re, k01re, k01im, k11re]
      refine ⟨by ring, by ring, ?_⟩
      linear_combination hα2 - hγ2 - hrad
  · have hk2 : k0 + k 2 = 0 := by nlinarith [sq_nonneg (k 0), sq_nonneg (k 1)]
    have hk01 : k 0 = 0 ∧ k 1 = 0 := by
      have : k 0 ^ 2 + k 1 ^ 2 ≤ 0 := by
        have : k 2 = -k0 := by linarith
        rw [this] at hc; nlinarith
      constructor <;> nlinarith [sq_nonneg (k 0), sq_nonneg (k 1)]
    set φ : HiggsMat := !![0, 0; 0, ((Real.sqrt k0 : ℝ) : ℂ)] with hφ
    have hsq : Real.sqrt k0 * Real.sqrt k0 = k0 := Real.mul_self_sqrt h0
    refine ⟨φ, ?_, ?_⟩
    · rw [W7b_THDM_K0_eq]
      simp [hφ, Complex.normSq_ofReal, hsq]
    · rw [hK]
      simp [W7b_THDM_K_apply, hφ]
      refine ⟨hk01.1.symm, hk01.2.symm, ?_⟩
      have : ((Real.sqrt k0 : ℂ) * (Real.sqrt k0 : ℂ)).re = k0 := by
        rw [← Complex.ofReal_mul, hsq, Complex.ofReal_re]
      linarith [this]

theorem solution :
    (∀ φ φ' : HiggsMat, Kmat φ = Kmat φ' → GaugeEquiv φ φ') ∧
    (∀ φ : HiggsMat, (K0 φ, Kvec φ) ∈ forwardCone) ∧
    (∀ p : ℝ × (Fin 3 → ℝ), p ∈ forwardCone →
        ∃ φ : HiggsMat, K0 φ = p.1 ∧ Kvec φ = p.2) :=
  ⟨W7b_THDM_part1, W7b_THDM_part2, W7b_THDM_part3⟩
