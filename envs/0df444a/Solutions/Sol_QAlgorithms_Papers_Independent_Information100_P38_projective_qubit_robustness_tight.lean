-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Information100.P38.projective_qubit_robustness_tight
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T08:21:41.189625+00:00
-- url     : https://prove2.me/submissions/a2eaad38-92d3-456f-90c1-d38e0aeaf250

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P38
noncomputable section

open scoped ComplexConjugate Matrix ComplexOrder

namespace X6P38Qubit

open QAlgorithms QAlgorithms.Papers.Independent.Information100.P38

def rq {d : ℕ} (W : Matrix (Fin d) (Fin d) ℂ) (v : EuclideanSpace ℂ (Fin d)) : ℝ :=
  (∑ i, ∑ j, conj (v i) * W i j * v j).re

def S {d : ℕ} (W : Matrix (Fin d) (Fin d) ℂ) : Set ℝ :=
  {r | ∃ v : EuclideanSpace ℂ (Fin d), IsState v ∧ r = rq W v}

lemma lee_eq {d : ℕ} (W : Matrix (Fin d) (Fin d) ℂ) : largestEnergyEigenvalue W = sSup (S W) := rfl

lemma state_sum {d : ℕ} (v : EuclideanSpace ℂ (Fin d)) (hv : IsState v) :
    ∑ i, ‖v i‖ ^ 2 = 1 := by
  unfold IsState at hv
  rw [EuclideanSpace.norm_eq, Real.sqrt_eq_one] at hv
  simpa using hv

lemma S_bdd {d : ℕ} (W : Matrix (Fin d) (Fin d) ℂ) : BddAbove (S W) := by
  refine ⟨∑ i, ∑ j, ‖W i j‖, ?_⟩
  rintro r ⟨v, hv, rfl⟩
  have h1 : ∀ i, ‖v i‖ ≤ 1 := fun i => by
    have := PiLp.norm_apply_le v i
    unfold IsState at hv; rw [hv] at this; exact this
  unfold rq
  refine (Complex.re_le_norm _).trans ((norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_))
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
  rw [norm_mul, norm_mul, Complex.norm_conj]
  have := h1 i; have := h1 j
  have := norm_nonneg (W i j); have := norm_nonneg (v i); have := norm_nonneg (v j)
  nlinarith [mul_le_mul_of_nonneg_left (h1 i) (norm_nonneg (W i j))]

lemma S_ne {d : ℕ} (hd : 0 < d) (W : Matrix (Fin d) (Fin d) ℂ) : (S W).Nonempty :=
  ⟨_, EuclideanSpace.single ⟨0, hd⟩ 1, by simp [IsState], rfl⟩

/-- Upper bound via a diagonalizing unitary. -/
lemma rq_le_of_diag {d : ℕ} (W V : Matrix (Fin d) (Fin d) ℂ) (hV : star V * V = 1)
    (μ : Fin d → ℝ) (hD : W = star V * Matrix.diagonal (fun i => (μ i : ℂ)) * V)
    (c : ℝ) (hc : ∀ i, μ i ≤ c) (v : EuclideanSpace ℂ (Fin d)) (hv : IsState v) :
    rq W v ≤ c := by
  have hq : ∀ (M : Matrix (Fin d) (Fin d) ℂ) (x : Fin d → ℂ),
      (∑ i, ∑ j, conj (x i) * M i j * x j) = star x ⬝ᵥ (M *ᵥ x) := by
    intro M x
    simp only [dotProduct, Matrix.mulVec, Finset.mul_sum, Pi.star_apply, RCLike.star_def,
      mul_assoc]
  set x : Fin d → ℂ := fun i => v i
  set w := V *ᵥ x
  have hx : ∑ i, Complex.normSq (x i) = 1 := by
    have := state_sum v hv
    simpa [x, Complex.normSq_eq_norm_sq] using this
  have hw : ∑ i, Complex.normSq (w i) = 1 := by
    have e : ∀ y : Fin d → ℂ, ((∑ i, Complex.normSq (y i) : ℝ) : ℂ) = star y ⬝ᵥ y := by
      intro y
      simp [dotProduct, Complex.normSq_eq_conj_mul_self]
    have : star w ⬝ᵥ w = star x ⬝ᵥ x := by
      simp only [w, Matrix.star_mulVec]
      rw [Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul, ← Matrix.star_eq_conjTranspose, hV,
        Matrix.vecMul_one]
    have h2 := e w
    rw [this, ← e x, hx] at h2
    exact_mod_cast h2
  have key : rq W v = ∑ i, μ i * Complex.normSq (w i) := by
    unfold rq
    rw [show (∑ i, ∑ j, conj (v i) * W i j * v j) = ∑ i, ∑ j, conj (x i) * W i j * x j from rfl,
      hq, hD]
    have : star x ⬝ᵥ ((star V * Matrix.diagonal (fun i => (μ i : ℂ)) * V) *ᵥ x) =
        star w ⬝ᵥ (Matrix.diagonal (fun i => (μ i : ℂ)) *ᵥ w) := by
      simp only [w, ← Matrix.mulVec_mulVec, Matrix.star_mulVec, Matrix.dotProduct_mulVec,
        Matrix.vecMul_vecMul]
      simp [Matrix.star_eq_conjTranspose]
    rw [this]
    simp only [dotProduct, Matrix.mulVec_diagonal, Pi.star_apply, RCLike.star_def]
    rw [Complex.re_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [Complex.mul_re, Complex.normSq_apply, Complex.conj_re, Complex.conj_im]
    ring
  rw [key]
  calc _ ≤ ∑ i, c * Complex.normSq (w i) :=
        Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (hc i) (Complex.normSq_nonneg _)
    _ = c := by rw [← Finset.mul_sum, hw, mul_one]


lemma row_state {d : ℕ} (U : Matrix.unitaryGroup (Fin d) ℂ) (k : Fin d) :
    IsState (WithLp.toLp 2 (fun j => conj ((U : Matrix (Fin d) (Fin d) ℂ) k j)) :
      EuclideanSpace ℂ (Fin d)) := by
  unfold IsState
  rw [EuclideanSpace.norm_eq, Real.sqrt_eq_one]
  have h := congrFun (congrFun (Matrix.mem_unitaryGroup_iff.mp U.2) k) k
  rw [Matrix.mul_apply] at h
  simp only [Matrix.star_apply, RCLike.star_def, Matrix.one_apply_eq] at h
  have h2 := congrArg Complex.re h
  rw [Complex.re_sum] at h2
  simp only [Complex.mul_conj, Complex.ofReal_re, Complex.one_re] at h2
  simpa [Complex.normSq_eq_norm_sq] using h2

lemma rq_row {d : ℕ} (W : Matrix (Fin d) (Fin d) ℂ) (U : Matrix.unitaryGroup (Fin d) ℂ)
    (k : Fin d) :
    rq W (WithLp.toLp 2 (fun j => conj ((U : Matrix (Fin d) (Fin d) ℂ) k j))) =
      (((U : Matrix (Fin d) (Fin d) ℂ) * W * (U : Matrix (Fin d) (Fin d) ℂ)ᴴ) k k).re := by
  unfold rq
  congr 1
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, RCLike.star_def, Complex.conj_conj,
    Finset.sum_mul]
  rw [Finset.sum_comm]

lemma bloch_quad_re (w : Fin 3 → ℝ) (x : Fin 2 → ℂ) :
    (star x ⬝ᵥ (ergotropicBlochMatrix w *ᵥ x)).re =
      (((x 0).re ^ 2 + (x 0).im ^ 2 + (x 1).re ^ 2 + (x 1).im ^ 2) +
        (w 2 * ((x 0).re ^ 2 + (x 0).im ^ 2 - (x 1).re ^ 2 - (x 1).im ^ 2) +
          2 * w 0 * ((x 0).re * (x 1).re + (x 0).im * (x 1).im) +
          2 * w 1 * ((x 0).re * (x 1).im - (x 0).im * (x 1).re))) / 2 := by
  simp [ergotropicBlochMatrix, dotProduct, Matrix.mulVec, Fin.sum_univ_two, Complex.mul_re,
    Complex.mul_im, Complex.div_re, Complex.div_im]
  ring

lemma bloch_quad_im (w : Fin 3 → ℝ) (x : Fin 2 → ℂ) :
    (star x ⬝ᵥ (ergotropicBlochMatrix w *ᵥ x)).im = 0 := by
  simp [ergotropicBlochMatrix, dotProduct, Matrix.mulVec, Fin.sum_univ_two, Complex.mul_re,
    Complex.mul_im, Complex.div_re, Complex.div_im]
  ring


lemma cs_bloch (w : Fin 3 → ℝ) (p q s u : ℝ) :
    |w 2 * (p ^ 2 + q ^ 2 - s ^ 2 - u ^ 2) + 2 * w 0 * (p * s + q * u) +
        2 * w 1 * (p * u - q * s)| ≤
      Real.sqrt (ergotropicBlochLengthSquared w) * (p ^ 2 + q ^ 2 + s ^ 2 + u ^ 2) := by
  have hN : 0 ≤ p ^ 2 + q ^ 2 + s ^ 2 + u ^ 2 := by positivity
  rw [← Real.sqrt_sq hN, ← Real.sqrt_mul (by unfold ergotropicBlochLengthSquared; positivity)]
  apply Real.abs_le_sqrt
  unfold ergotropicBlochLengthSquared
  simp only [Fin.sum_univ_three]
  set y0 := p ^ 2 + q ^ 2 - s ^ 2 - u ^ 2
  set y1 := 2 * (p * s + q * u)
  set y2 := 2 * (p * u - q * s)
  have hy : y0 ^ 2 + y1 ^ 2 + y2 ^ 2 = (p ^ 2 + q ^ 2 + s ^ 2 + u ^ 2) ^ 2 := by
    simp only [y0, y1, y2]; ring
  have e : w 2 * y0 + 2 * w 0 * (p * s + q * u) + 2 * w 1 * (p * u - q * s) =
      w 2 * y0 + w 0 * y1 + w 1 * y2 := by simp only [y1, y2]; ring
  rw [e, ← hy]
  nlinarith [sq_nonneg (w 2 * y1 - w 0 * y0), sq_nonneg (w 2 * y2 - w 1 * y0),
    sq_nonneg (w 0 * y2 - w 1 * y1)]

lemma bloch_herm (w : Fin 3 → ℝ) : (ergotropicBlochMatrix w).IsHermitian := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [ergotropicBlochMatrix, Complex.ext_iff, Complex.conj_re, Complex.conj_im]

lemma bloch_trace (w : Fin 3 → ℝ) : (ergotropicBlochMatrix w).trace = 1 := by
  rw [Matrix.trace_fin_two]
  simp [ergotropicBlochMatrix]
  ring

lemma bloch_psd (w : Fin 3 → ℝ) (hw : ergotropicBlochLengthSquared w ≤ 1) :
    (ergotropicBlochMatrix w).PosSemidef := by
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg (bloch_herm w) fun x => ?_
  rw [Complex.nonneg_iff, bloch_quad_re, bloch_quad_im]
  refine ⟨?_, rfl⟩
  have h := cs_bloch w (x 0).re (x 0).im (x 1).re (x 1).im
  have hr : Real.sqrt (ergotropicBlochLengthSquared w) ≤ 1 := Real.sqrt_le_one.mpr hw
  have hN : 0 ≤ (x 0).re ^ 2 + (x 0).im ^ 2 + (x 1).re ^ 2 + (x 1).im ^ 2 := by positivity
  have h2 := abs_le.mp h
  nlinarith [mul_le_mul_of_nonneg_right hr hN]

lemma rq_bloch_le (w : Fin 3 → ℝ) (v : EuclideanSpace ℂ (Fin 2)) (hv : IsState v) :
    rq (ergotropicBlochMatrix w) v ≤ (1 + Real.sqrt (ergotropicBlochLengthSquared w)) / 2 := by
  have hs := state_sum v hv
  simp only [Fin.sum_univ_two, ← Complex.normSq_eq_norm_sq, Complex.normSq_apply] at hs
  have e : rq (ergotropicBlochMatrix w) v =
      (star (fun i => v i) ⬝ᵥ (ergotropicBlochMatrix w *ᵥ (fun i => v i))).re := by
    unfold rq
    congr 1
    simp only [dotProduct, Matrix.mulVec, Finset.mul_sum, Pi.star_apply, RCLike.star_def, mul_assoc]
  rw [e, bloch_quad_re]
  have h := abs_le.mp (cs_bloch w (v 0).re (v 0).im (v 1).re (v 1).im)
  have hN : (v 0).re ^ 2 + (v 0).im ^ 2 + (v 1).re ^ 2 + (v 1).im ^ 2 = 1 := by nlinarith
  rw [hN] at h
  simp only [] at *
  nlinarith

lemma eig_le_lee {d : ℕ} (W : Matrix (Fin d) (Fin d) ℂ) (hW : W.IsHermitian) (i : Fin d) :
    hW.eigenvalues i ≤ largestEnergyEigenvalue W := by
  rw [lee_eq]
  refine le_csSup (S_bdd W) ⟨hW.eigenvectorBasis i, ?_, ?_⟩
  · exact (hW.eigenvectorBasis.orthonormal.1 i)
  · rw [hW.eigenvalues_eq i]
    unfold rq
    simp only [dotProduct, Matrix.mulVec, Finset.mul_sum, Pi.star_apply, RCLike.star_def,
      mul_assoc, RCLike.re_to_complex]

lemma lee_bloch (w : Fin 3 → ℝ) :
    largestEnergyEigenvalue (ergotropicBlochMatrix w) =
      (1 + Real.sqrt (ergotropicBlochLengthSquared w)) / 2 := by
  apply le_antisymm
  · rw [lee_eq]
    exact csSup_le (S_ne (by norm_num) _) (by rintro r ⟨v, hv, rfl⟩; exact rq_bloch_le w v hv)
  · have hW := bloch_herm w
    have ht := hW.trace_eq_sum_eigenvalues
    have hd := hW.det_eq_prod_eigenvalues
    have e0 := eig_le_lee _ hW 0
    have e1 := eig_le_lee _ hW 1
    set μ0 := hW.eigenvalues 0
    set μ1 := hW.eigenvalues 1
    rw [bloch_trace, Fin.sum_univ_two] at ht
    rw [Fin.prod_univ_two, Matrix.det_fin_two] at hd
    have ht2 : (1 : ℂ) = (μ0 : ℂ) + (μ1 : ℂ) := ht
    have hd2 : ergotropicBlochMatrix w 0 0 * ergotropicBlochMatrix w 1 1 -
        ergotropicBlochMatrix w 0 1 * ergotropicBlochMatrix w 1 0 = (μ0 : ℂ) * (μ1 : ℂ) := hd
    have ht' := congrArg Complex.re ht2
    have hd' := congrArg Complex.re hd2
    have hdet : (ergotropicBlochMatrix w 0 0 * ergotropicBlochMatrix w 1 1 -
        ergotropicBlochMatrix w 0 1 * ergotropicBlochMatrix w 1 0).re =
        (1 - w 0 ^ 2 - w 1 ^ 2 - w 2 ^ 2) / 4 := by
      simp [ergotropicBlochMatrix, Complex.mul_re, Complex.div_re]
      ring
    rw [hdet] at hd'
    simp only [Complex.add_re, Complex.ofReal_re, Complex.one_re, Complex.mul_re,
      Complex.ofReal_im, mul_zero, sub_zero] at ht' hd'
    set r := Real.sqrt (ergotropicBlochLengthSquared w)
    have hr2 : r ^ 2 = w 0 ^ 2 + w 1 ^ 2 + w 2 ^ 2 := by
      rw [Real.sq_sqrt (by unfold ergotropicBlochLengthSquared; positivity)]
      simp [ergotropicBlochLengthSquared, Fin.sum_univ_three]
    have hr0 : 0 ≤ r := Real.sqrt_nonneg _
    have hsq : (μ0 - μ1) ^ 2 = r ^ 2 := by nlinarith
    rcases le_total μ1 μ0 with h | h
    · have : μ0 - μ1 = r := by
        have := (pow_left_inj₀ (by linarith) hr0 (by norm_num : (2:ℕ) ≠ 0)).mp hsq
        exact this
      linarith
    · have : μ1 - μ0 = r := by
        have := (pow_left_inj₀ (by linarith) hr0 (by norm_num : (2:ℕ) ≠ 0)).mp
          (by rw [← hsq]; ring : (μ1 - μ0) ^ 2 = r ^ 2)
        exact this
      linarith


lemma passive2 (W : Matrix (Fin 2) (Fin 2) ℂ) (hW : W.IsHermitian) (htr : W.trace = 1)
    (E : ℝ) (hE : 0 ≤ E) :
    passiveEnergy ![0, E] W = E * (1 - largestEnergyEigenvalue W) := by
  unfold passiveEnergy
  rw [lee_eq]
  set l1 := sSup (S W)
  have hEE : ∀ Z : Matrix (Fin 2) (Fin 2) ℂ, Z.trace = 1 →
      energyExpectation ![0, E] Z = E * (1 - (Z 0 0).re) := by
    intro Z hZ
    have := congrArg Complex.re hZ
    rw [Matrix.trace_fin_two] at this
    simp only [Complex.add_re, Complex.one_re] at this
    unfold energyExpectation
    simp [Fin.sum_univ_two]
    left; linarith
  have htrU : ∀ U : Matrix.unitaryGroup (Fin 2) ℂ,
      ((U : Matrix (Fin 2) (Fin 2) ℂ) * W * (U : Matrix (Fin 2) (Fin 2) ℂ)ᴴ).trace = 1 := by
    intro U
    rw [Matrix.trace_mul_comm, ← mul_assoc, ← Matrix.star_eq_conjTranspose,
      Unitary.star_mul_self_of_mem U.2, one_mul, htr]
  have hlow : ∀ U : Matrix.unitaryGroup (Fin 2) ℂ, E * (1 - l1) ≤
      energyExpectation ![0, E] ((U : Matrix (Fin 2) (Fin 2) ℂ) * W *
        (U : Matrix (Fin 2) (Fin 2) ℂ)ᴴ) := by
    intro U
    rw [hEE _ (htrU U)]
    have h0 : (((U : Matrix (Fin 2) (Fin 2) ℂ) * W * (U : Matrix (Fin 2) (Fin 2) ℂ)ᴴ) 0 0).re
        ≤ l1 := le_csSup (S_bdd W) ⟨_, row_state U 0, (rq_row W U 0).symm⟩
    exact mul_le_mul_of_nonneg_left (by linarith) hE
  set E' := hW.eigenvectorUnitary
  set μ := hW.eigenvalues
  have hdiag : star (E' : Matrix (Fin 2) (Fin 2) ℂ) * W * (E' : Matrix (Fin 2) (Fin 2) ℂ) =
      Matrix.diagonal (fun i => (μ i : ℂ)) := by
    have h := hW.conjStarAlgAut_star_eigenvectorUnitary
    simp at h
    exact h
  set σ : Equiv.Perm (Fin 2) := Fin.revPerm.trans (Tuple.sort μ)
  have hmono := Tuple.monotone_sort μ
  have hσ0 : ∀ i, μ (σ i) ≤ μ (σ 0) := fun i =>
    hmono (show Fin.rev i ≤ Fin.rev 0 by fin_cases i <;> decide)
  set V : Matrix (Fin 2) (Fin 2) ℂ := (star (E' : Matrix (Fin 2) (Fin 2) ℂ)).submatrix σ id
  have hVs : star V = (E' : Matrix (Fin 2) (Fin 2) ℂ).submatrix id σ := by
    simp [V, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_submatrix]
  have hVV : V * star V = 1 := by
    rw [hVs]
    ext i j
    simp only [V, Matrix.mul_apply, Matrix.submatrix_apply, id]
    have h := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M (σ i) (σ j))
      (Unitary.star_mul_self_of_mem E'.2)
    simp only [Matrix.mul_apply] at h
    rw [h]
    simp [Matrix.one_apply, σ.injective.eq_iff]
  have hVV' : star V * V = 1 := mul_eq_one_comm.mp hVV
  have hVU : V ∈ Matrix.unitaryGroup (Fin 2) ℂ := Matrix.mem_unitaryGroup_iff.mpr hVV
  have hZ : V * W * star V = Matrix.diagonal (fun i => (μ (σ i) : ℂ)) := by
    rw [hVs]
    have : V * W * (E' : Matrix (Fin 2) (Fin 2) ℂ).submatrix id σ =
        (star (E' : Matrix (Fin 2) (Fin 2) ℂ) * W * (E' : Matrix (Fin 2) (Fin 2) ℂ)).submatrix σ σ := by
      ext i j
      simp [V, Matrix.mul_apply]
    rw [this, hdiag, Matrix.submatrix_diagonal_equiv]
    rfl
  have hWd : W = star V * Matrix.diagonal (fun i => (μ (σ i) : ℂ)) * V := by
    rw [← hZ, ← mul_assoc, ← mul_assoc, hVV', one_mul, mul_assoc, hVV', mul_one]
  have hl1 : l1 ≤ μ (σ 0) := csSup_le (S_ne (by norm_num) W) (by
    rintro r ⟨v, hv, rfl⟩
    exact rq_le_of_diag W V hVV' _ hWd _ hσ0 v hv)
  have hatt : energyExpectation ![0, E] ((⟨V, hVU⟩ : Matrix.unitaryGroup (Fin 2) ℂ) *
      W * ((⟨V, hVU⟩ : Matrix.unitaryGroup (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ)ᴴ) ≤
      E * (1 - l1) := by
    rw [hEE _ (htrU _)]
    show E * (1 - ((V * W * Vᴴ) 0 0).re) ≤ _
    rw [← Matrix.star_eq_conjTranspose, hZ]
    simp
    exact mul_le_mul_of_nonneg_left (by linarith) hE
  have hmem : energyExpectation ![0, E] ((⟨V, hVU⟩ : Matrix.unitaryGroup (Fin 2) ℂ) *
      W * ((⟨V, hVU⟩ : Matrix.unitaryGroup (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ)ᴴ) ∈
      {r | ∃ U : Matrix.unitaryGroup (Fin 2) ℂ, r = energyExpectation ![0, E]
        ((U : Matrix (Fin 2) (Fin 2) ℂ) * W * (U : Matrix (Fin 2) (Fin 2) ℂ)ᴴ)} := ⟨_, rfl⟩
  apply le_antisymm
  · exact (csInf_le ⟨E * (1 - l1), by rintro r ⟨U, rfl⟩; exact hlow U⟩ hmem).trans hatt
  · exact le_csInf ⟨_, hmem⟩ (by rintro r ⟨U, rfl⟩; exact hlow U)

lemma bloch_neg (m : Fin 3 → ℝ) : 1 - ergotropicBlochMatrix m = ergotropicBlochMatrix (-m) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [ergotropicBlochMatrix] <;> ring

lemma len_neg (m : Fin 3 → ℝ) : ergotropicBlochLengthSquared (-m) = ergotropicBlochLengthSquared m := by
  simp [ergotropicBlochLengthSquared]

lemma energy_bloch (E : ℝ) (v : Fin 3 → ℝ) :
    energyExpectation ![0, E] (ergotropicBlochMatrix v) = E * ((1 - v 2) / 2) := by
  simp [energyExpectation, Fin.sum_univ_two, ergotropicBlochMatrix]

end X6P38Qubit

namespace X6P38Qubit
open QAlgorithms QAlgorithms.Papers.Independent.Information100.P38

lemma bloch_of_density (X : Matrix (Fin 2) (Fin 2) ℂ) (hX : IsDensityMatrix X) :
    ∃ v, ergotropicBlochLengthSquared v ≤ 1 ∧ X = ergotropicBlochMatrix v := by
  have hH := hX.1.isHermitian
  have h00 : X 0 0 = ((X 0 0).re : ℂ) := (Complex.conj_eq_iff_re.mp (hH.apply 0 0)).symm
  have h11 : X 1 1 = ((X 1 1).re : ℂ) := (Complex.conj_eq_iff_re.mp (hH.apply 1 1)).symm
  have h01 : X 0 1 = star (X 1 0) := (hH.apply 0 1).symm
  have htr := congrArg Complex.re hX.2
  rw [Matrix.trace_fin_two] at htr
  simp only [Complex.add_re, Complex.one_re] at htr
  have hdet := hX.1.det_nonneg
  rw [Matrix.det_fin_two, h01, h00, h11] at hdet
  rw [Complex.nonneg_iff] at hdet
  simp [Complex.mul_re, Complex.conj_re, Complex.conj_im] at hdet
  refine ⟨![2 * (X 1 0).re, 2 * (X 1 0).im, (X 0 0).re - (X 1 1).re], ?_, ?_⟩
  · simp [ergotropicBlochLengthSquared, Fin.sum_univ_three]
    nlinarith [hdet.1]
  · ext i j
    fin_cases i <;> fin_cases j
    · simp [ergotropicBlochMatrix]
      rw [h00]; apply Complex.ext <;> simp; linarith
    · simp [ergotropicBlochMatrix]
      rw [h01]; apply Complex.ext <;> simp [Complex.conj_re, Complex.conj_im] <;> ring
    · simp [ergotropicBlochMatrix]
      apply Complex.ext <;> simp
    · simp [ergotropicBlochMatrix]
      rw [h11]; apply Complex.ext <;> simp; linarith


lemma coarse_binary (m v : Fin 3 → ℝ) :
    ergotropicCoarseGraining (ergotropicBlochMeasurement m) (ergotropicBlochMatrix v) =
      ergotropicBlochMatrix (ergotropicBlochDot v m • m) := by
  simp only [ergotropicCoarseGraining, ergotropicBlochMeasurement, ergotropicBinary,
    Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, bloch_neg, bloch_trace,
    one_ne_zero, if_false, div_one]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [ergotropicBlochMatrix, Matrix.trace_fin_two, ergotropicBlochDot, Fin.sum_univ_three,
      Complex.ext_iff] <;>
    constructor <;> ring_nf

lemma len_smul (c : ℝ) (m : Fin 3 → ℝ) :
    Real.sqrt (ergotropicBlochLengthSquared (c • m)) =
      |c| * Real.sqrt (ergotropicBlochLengthSquared m) := by
  have : ergotropicBlochLengthSquared (c • m) = c ^ 2 * ergotropicBlochLengthSquared m := by
    simp only [ergotropicBlochLengthSquared, Pi.smul_apply, smul_eq_mul, mul_pow,
      ← Finset.mul_sum]
  rw [this, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq_eq_abs]

lemma obs_binary (E : ℝ) (hE : 0 ≤ E) (m v : Fin 3 → ℝ) :
    observationalErgotropy ![0, E] (ergotropicBlochMeasurement m) (ergotropicBlochMatrix v) =
      E / 2 * (|ergotropicBlochDot v m| * Real.sqrt (ergotropicBlochLengthSquared m) - v 2) := by
  unfold observationalErgotropy
  rw [coarse_binary, passive2 _ (bloch_herm _) (bloch_trace _) E hE, lee_bloch, len_smul,
    energy_bloch]
  ring

lemma inc_bloch (E : ℝ) (hE : 0 ≤ E) (v : Fin 3 → ℝ) :
    incoherentErgotropy ![0, E] (ergotropicBlochMatrix v) = E / 2 * (|v 2| - v 2) := by
  have hdeph : energyDephasing (ergotropicBlochMatrix v) = ergotropicBlochMatrix ![0, 0, v 2] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [energyDephasing, ergotropicBlochMatrix]
  have hlen2 : Real.sqrt (ergotropicBlochLengthSquared ![0, 0, v 2]) = |v 2| := by
    simp [ergotropicBlochLengthSquared, Fin.sum_univ_three, Real.sqrt_sq_eq_abs]
  unfold incoherentErgotropy
  rw [hdeph, passive2 _ (bloch_herm _) (bloch_trace _) E hE, lee_bloch, hlen2, energy_bloch]
  simp
  ring

lemma adv_eq {n : ℕ} (E : ℝ) (M : Fin n → Matrix (Fin 2) (Fin 2) ℂ) (f : (Fin 3 → ℝ) → ℝ)
    (hf : ∀ v, ergotropicBlochLengthSquared v ≤ 1 →
      observationalErgotropy ![0, E] M (ergotropicBlochMatrix v) -
        incoherentErgotropy ![0, E] (ergotropicBlochMatrix v) = f v) :
    observationalAdvantage ![0, E] M =
      sSup {r | ∃ v, ergotropicBlochLengthSquared v ≤ 1 ∧ r = f v} := by
  unfold observationalAdvantage
  congr 1
  ext r
  constructor
  · rintro ⟨X, hX, rfl⟩
    obtain ⟨v, hv, rfl⟩ := bloch_of_density X hX
    exact ⟨v, hv, hf v hv⟩
  · rintro ⟨v, hv, rfl⟩
    exact ⟨_, ⟨bloch_psd v hv, bloch_trace v⟩, (hf v hv).symm⟩

lemma perp_le (v m : Fin 3 → ℝ) (hv : ergotropicBlochLengthSquared v ≤ 1) :
    |v 0 * m 0 + v 1 * m 1| ≤ Real.sqrt (m 0 ^ 2 + m 1 ^ 2) := by
  have hv' : v 0 ^ 2 + v 1 ^ 2 ≤ 1 := by
    simp [ergotropicBlochLengthSquared, Fin.sum_univ_three] at hv; nlinarith [sq_nonneg (v 2)]
  apply Real.abs_le_sqrt
  nlinarith [sq_nonneg (v 0 * m 1 - v 1 * m 0), sq_nonneg (m 0), sq_nonneg (m 1)]

lemma bloch_povm (m : Fin 3 → ℝ) (hm : ergotropicBlochLengthSquared m ≤ 1) :
    IsPOVM (ergotropicBlochMeasurement m) := by
  refine ⟨fun o => ?_, ?_⟩
  · fin_cases o
    · exact bloch_psd m hm
    · show (1 - ergotropicBlochMatrix m).PosSemidef
      rw [bloch_neg]
      exact bloch_psd _ (by rw [len_neg]; exact hm)
  · simp [ergotropicBlochMeasurement, ergotropicBinary, Fin.sum_univ_two]

lemma norm_half (a b : ℝ) : ‖((a : ℂ) - Complex.I * (b : ℂ)) / 2‖ = Real.sqrt (a ^ 2 + b ^ 2) / 2 := by
  rw [norm_div, Complex.norm_def]
  simp [Complex.normSq_apply]
  ring_nf

end X6P38Qubit
namespace X6P38Qubit
open QAlgorithms QAlgorithms.Papers.Independent.Information100.P38

lemma psd2 (A : Matrix (Fin 2) (Fin 2) ℂ) (hA : A.PosSemidef) :
    ‖A 0 1‖ ^ 2 ≤ (A 0 0).re * (A 1 1).re ∧ 0 ≤ (A 0 0).re ∧ 0 ≤ (A 1 1).re := by
  have hH := hA.isHermitian
  have h10 : A 1 0 = star (A 0 1) := (hH.apply 1 0).symm
  have h00 : A 0 0 = ((A 0 0).re : ℂ) := (Complex.conj_eq_iff_re.mp (hH.apply 0 0)).symm
  have h11 : A 1 1 = ((A 1 1).re : ℂ) := (Complex.conj_eq_iff_re.mp (hH.apply 1 1)).symm
  have hdet := hA.det_nonneg
  rw [Matrix.det_fin_two, h10, h00, h11, Complex.nonneg_iff] at hdet
  simp [Complex.mul_re, Complex.conj_re, Complex.conj_im] at hdet
  have hd0 := (Complex.nonneg_iff.mp (hA.diag_nonneg (i := 0))).1
  have hd1 := (Complex.nonneg_iff.mp (hA.diag_nonneg (i := 1))).1
  refine ⟨?_, hd0, hd1⟩
  rw [Complex.sq_norm, Complex.normSq_apply]
  nlinarith [hdet.1]

lemma linf_binary (m : Fin 3 → ℝ) :
    measurementLinfCoherence (ergotropicBlochMeasurement m) = Real.sqrt (m 0 ^ 2 + m 1 ^ 2) := by
  unfold measurementLinfCoherence
  have : {r | ∃ i j : Fin 2, i < j ∧
      r = ∑ u, ‖ergotropicBlochMeasurement m u i j‖} = {Real.sqrt (m 0 ^ 2 + m 1 ^ 2)} := by
    ext r
    simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff]
    have hval : ∑ u, ‖ergotropicBlochMeasurement m u 0 1‖ = Real.sqrt (m 0 ^ 2 + m 1 ^ 2) := by
      simp only [Fin.sum_univ_two, ergotropicBlochMeasurement, ergotropicBinary,
        Matrix.cons_val_zero, Matrix.cons_val_one, bloch_neg]
      simp only [ergotropicBlochMatrix, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one, Pi.neg_apply]
      rw [norm_half]
      have : ((((-m 0 : ℝ) : ℂ) - Complex.I * ((-m 1 : ℝ) : ℂ)) / 2) =
          -((((m 0 : ℝ) : ℂ) - Complex.I * ((m 1 : ℝ) : ℂ)) / 2) := by push_cast; ring
      rw [this, norm_neg, norm_half]
      ring
    constructor
    · rintro ⟨i, j, hij, rfl⟩
      fin_cases i <;> fin_cases j <;> simp at hij
      exact hval
    · rintro rfl
      exact ⟨0, 1, by decide, hval.symm⟩
  rw [this, csSup_singleton]

end X6P38Qubit
namespace X6P38Qubit
open QAlgorithms QAlgorithms.Papers.Independent.Information100.P38

lemma meas0 (m : Fin 3 → ℝ) : ergotropicBlochMeasurement m 0 = ergotropicBlochMatrix m := rfl
lemma meas1 (m : Fin 3 → ℝ) : ergotropicBlochMeasurement m 1 = ergotropicBlochMatrix (-m) := by
  show 1 - ergotropicBlochMatrix m = _
  rw [bloch_neg]

lemma q_le_half (a b q : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (ha1 : 0 ≤ 1 - a) (hb1 : 0 ≤ 1 - b)
    (hq : 0 ≤ q) (h1 : q ^ 2 ≤ a * b) (h2 : q ^ 2 ≤ (1 - a) * (1 - b)) : q ≤ 1 / 2 := by
  by_contra hc
  push Not at hc
  nlinarith [sq_nonneg (a - b), sq_nonneg (a + b - 1)]

lemma rob_binary (m : Fin 3 → ℝ) (hm : ergotropicBlochLengthSquared m ≤ 1) :
    measurementCoherenceRobustness (ergotropicBlochMeasurement m) =
      Real.sqrt (m 0 ^ 2 + m 1 ^ 2) := by
  set k := Real.sqrt (m 0 ^ 2 + m 1 ^ 2) with hkdef
  have hk0 : 0 ≤ k := Real.sqrt_nonneg _
  have hk2 : k ^ 2 = m 0 ^ 2 + m 1 ^ 2 := Real.sq_sqrt (by positivity)
  unfold measurementCoherenceRobustness
  apply IsLeast.csInf_eq
  constructor
  · refine ⟨hk0, ?_⟩
    rcases hk0.lt_or_eq with hk | hk
    · set w : Fin 3 → ℝ := ![m 0 / k, m 1 / k, 0]
      have hw : ergotropicBlochLengthSquared w ≤ 1 := by
        simp only [ergotropicBlochLengthSquared, Fin.sum_univ_three, w]
        simp
        rw [div_pow, div_pow, ← add_div, ← hk2, div_self (by positivity)]
      have hP := bloch_povm (-w) (by rw [len_neg]; exact hw)
      set c : ℂ := (((1 + k : ℝ)⁻¹ : ℝ) : ℂ)
      have hc0 : (0 : ℂ) ≤ c := Complex.zero_le_real.mpr (by positivity)
      refine ⟨ergotropicBlochMeasurement (-w),
        fun u => c • (ergotropicBlochMeasurement m u + (k : ℂ) • ergotropicBlochMeasurement (-w) u),
        hP, ⟨fun u => ?_, ?_⟩, fun u => ?_, fun u => ?_⟩
      · exact ((bloch_povm m hm).1 u |>.add ((hP.1 u).smul
          (Complex.zero_le_real.mpr hk0))).smul hc0
      · rw [← Finset.smul_sum, Finset.sum_add_distrib, ← Finset.smul_sum, (bloch_povm m hm).2,
          hP.2]
        have e1 : (1 : Matrix (Fin 2) (Fin 2) ℂ) + (k : ℂ) • 1 = ((1 + k : ℝ) : ℂ) • 1 := by
          rw [Complex.ofReal_add, add_smul]; simp
        rw [e1, smul_smul]
        simp only [c]
        rw [← Complex.ofReal_mul, inv_mul_cancel₀ (by positivity)]
        simp
      · have hkne : (k : ℂ) ≠ 0 := by exact_mod_cast hk.ne'
        ext i j
        fin_cases u <;> fin_cases i <;> fin_cases j <;>
          simp [energyDephasing, meas0, meas1, ergotropicBlochMatrix, w] <;>
          field_simp <;> ring_nf <;> simp
      · rw [smul_smul]
        simp only [c]
        rw [← Complex.ofReal_mul, mul_inv_cancel₀ (by positivity)]
        simp
    · have h0 : m 0 = 0 ∧ m 1 = 0 := by
        have : m 0 ^ 2 + m 1 ^ 2 = 0 := by rw [← hk2, ← hk]; ring
        constructor <;> nlinarith [sq_nonneg (m 0), sq_nonneg (m 1)]
      refine ⟨ergotropicBlochMeasurement m, ergotropicBlochMeasurement m, bloch_povm m hm,
        bloch_povm m hm, fun u => ?_, fun u => ?_⟩
      · ext i j
        fin_cases u <;> fin_cases i <;> fin_cases j <;>
          simp [energyDephasing, meas0, meas1, ergotropicBlochMatrix, h0.1, h0.2]
      · rw [← hk]; simp
  · rintro r ⟨hr, P, N, hP, hN, hNinc, heq⟩
    have hN01 : ∀ u, N u 0 1 = 0 := by
      intro u
      have := congrArg (fun A : Matrix (Fin 2) (Fin 2) ℂ => A 0 1) (hNinc u)
      simp [energyDephasing] at this
      exact this.symm
    have e0 := congrArg (fun A : Matrix (Fin 2) (Fin 2) ℂ => A 0 1) (heq 0)
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, hN01, mul_zero, meas0] at e0
    have hM : ‖ergotropicBlochMatrix m 0 1‖ = k / 2 := by
      simp only [ergotropicBlochMatrix, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one]
      rw [norm_half]
    have hnorm : k / 2 = r * ‖P 0 0 1‖ := by
      rw [← hM, eq_neg_of_add_eq_zero_left e0, norm_neg, norm_mul, Complex.norm_real,
        Real.norm_of_nonneg hr]
    have hP1 : P 1 = 1 - P 0 := by
      have := hP.2
      rw [Fin.sum_univ_two] at this
      rw [← this]; abel
    obtain ⟨h1, ha, hb⟩ := psd2 (P 0) (hP.1 0)
    obtain ⟨h2, ha1, hb1⟩ := psd2 (P 1) (hP.1 1)
    rw [hP1] at h2 ha1 hb1
    simp only [Matrix.sub_apply, Matrix.one_apply_eq, Complex.sub_re, Complex.one_re,
      norm_neg] at h2 ha1 hb1
    have h2' : ‖P 0 0 1‖ ^ 2 ≤ (1 - (P 0 0 0).re) * (1 - (P 0 1 1).re) := by
      simpa using h2
    have hq := q_le_half _ _ _ ha hb ha1 hb1 (norm_nonneg _) h1 h2'
    nlinarith

end X6P38Qubit

namespace X6P38Qubit
open QAlgorithms QAlgorithms.Papers.Independent.Information100.P38

lemma len_eq (v : Fin 3 → ℝ) : ergotropicBlochLengthSquared v = v 0 ^ 2 + v 1 ^ 2 + v 2 ^ 2 := by
  simp [ergotropicBlochLengthSquared, Fin.sum_univ_three]

lemma dot_eq (v m : Fin 3 → ℝ) : ergotropicBlochDot v m = v 0 * m 0 + v 1 * m 1 + v 2 * m 2 := by
  simp [ergotropicBlochDot, Fin.sum_univ_three]

/-- the unit transverse direction attains the transverse length -/
lemma perp_attain (m : Fin 3 → ℝ) :
    ∃ v : Fin 3 → ℝ, ergotropicBlochLengthSquared v ≤ 1 ∧ v 2 = 0 ∧
      v 0 * m 0 + v 1 * m 1 = Real.sqrt (m 0 ^ 2 + m 1 ^ 2) := by
  set k := Real.sqrt (m 0 ^ 2 + m 1 ^ 2)
  have hk0 : 0 ≤ k := Real.sqrt_nonneg _
  have hk2 : k ^ 2 = m 0 ^ 2 + m 1 ^ 2 := Real.sq_sqrt (by positivity)
  rcases hk0.lt_or_eq with hk | hk
  · refine ⟨![m 0 / k, m 1 / k, 0], ?_, rfl, ?_⟩
    · rw [len_eq]; simp
      rw [div_pow, div_pow, ← add_div, ← hk2, div_self (by positivity)]
    · simp
      field_simp
      linarith
  · refine ⟨0, by simp [len_eq], rfl, ?_⟩
    simp [← hk]

end X6P38Qubit

open X6P38Qubit QAlgorithms QAlgorithms.Papers.Independent.Information100.P38 in
theorem solution (E : ℝ) (hE : 0 < E)
    (m : Fin 3 → ℝ) (hm : ergotropicBlochLengthSquared m = 1) :
    let M := ergotropicBlochMeasurement m
    IsPOVM M ∧ observationalAdvantage ![0, E] M = E / 2 * Real.sqrt ((m 0)^2 + (m 1)^2) ∧
      observationalAdvantage ![0, E] M = E / 2 * measurementLinfCoherence M ∧
      observationalAdvantage ![0, E] M = E / 2 * measurementCoherenceRobustness M := by
  intro M
  have hadv : observationalAdvantage ![0, E] M = E / 2 * Real.sqrt ((m 0)^2 + (m 1)^2) := by
    rw [adv_eq E M (fun v => E / 2 * (|ergotropicBlochDot v m| - |v 2|)) (fun v hv => by
      rw [obs_binary E hE.le, inc_bloch E hE.le, hm, Real.sqrt_one]; ring)]
    apply IsGreatest.csSup_eq
    constructor
    · obtain ⟨v, hv, hv2, hvm⟩ := perp_attain m
      refine ⟨v, hv, ?_⟩
      rw [dot_eq, hv2, ← hvm]
      simp [abs_of_nonneg (hvm ▸ Real.sqrt_nonneg _ : (0:ℝ) ≤ v 0 * m 0 + v 1 * m 1)]
    · rintro r ⟨v, hv, rfl⟩
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      have h1 := perp_le v m hv
      have hm2 : |m 2| ≤ 1 := by
        rw [len_eq] at hm
        rw [← Real.sqrt_sq_eq_abs, ← Real.sqrt_one]
        exact Real.sqrt_le_sqrt (by nlinarith [sq_nonneg (m 0), sq_nonneg (m 1)])
      rw [dot_eq]
      have h3 := abs_add_le (v 0 * m 0 + v 1 * m 1) (v 2 * m 2)
      rw [abs_mul (v 2)] at h3
      have : |v 2| * |m 2| ≤ |v 2| := mul_le_of_le_one_right (abs_nonneg _) hm2
      linarith
  exact ⟨bloch_povm m hm.le, hadv, by rw [hadv, linf_binary], by rw [hadv, rob_binary m hm.le]⟩
