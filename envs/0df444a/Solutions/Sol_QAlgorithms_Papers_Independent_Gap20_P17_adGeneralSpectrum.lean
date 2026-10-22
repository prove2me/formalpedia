-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Gap20.P17.adGeneralSpectrum
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T22:14:30.789035+00:00
-- url     : https://prove2.me/submissions/f58b4c16-6212-499a-a47f-02bfb32cd3d3

import Definitions.Def_QAlgorithms_Papers_Independent_Gap20_P17
noncomputable section

open QAlgorithms.Papers.Independent.Gap20.P17

open scoped Matrix ComplexConjugate

open Filter

open QAlgorithms.Papers.Independent.Information100.P67
  (IsIsometry receiverChannel complementaryChannel IsDegradable IsAntidegradable dilationPower)

open QAlgorithms.Papers.Independent.Dependency50.P09 (erasureFin entangledPhi tensorAction)

open QAlgorithms.Papers.Independent.Claimed50.P24 (productDilation)

attribute [local instance] Classical.propDecidable Classical.decEq
open QAlgorithms

lemma g73g_cfc_trace {n : Type*} [Fintype n] [DecidableEq n] {Y : Matrix n n ℂ} (hY : Y.IsHermitian)
    (f : ℝ → ℝ) : (cfc f Y).trace = ∑ i, ((f (hY.eigenvalues i) : ℝ) : ℂ) := by
  rw [hY.cfc_eq f, Matrix.IsHermitian.cfc, Unitary.conjStarAlgAut_apply, Matrix.trace_mul_cycle,
    Unitary.star_mul_self_of_mem hY.eigenvectorUnitary.2, one_mul, Matrix.trace_diagonal]
  rfl

lemma g73g_trace_cfc_spec {n : Type} [Fintype n] [DecidableEq n] {k : ℕ} (M : Matrix n n ℂ)
    (hM : M.IsHermitian) (lam : Fin k → ℝ) (h : HasSpectrum M lam) (f : ℝ → ℝ) :
    (cfc f M).trace = ∑ j, ((f (lam j) : ℝ) : ℂ) := by
  rw [g73g_cfc_trace hM]
  have h1 := hM.roots_charpoly_eq_eigenvalues
  rw [h, Polynomial.roots_prod _ _ (by
    simp [Finset.prod_ne_zero_iff, Polynomial.X_sub_C_ne_zero])] at h1
  simp only [Polynomial.roots_X_sub_C] at h1
  have h2 : Multiset.map (fun i => (lam i : ℂ)) Finset.univ.val =
      Multiset.map (fun i => ((hM.eigenvalues i : ℝ) : ℂ)) Finset.univ.val := by
    have := h1
    rw [Multiset.bind_singleton] at this
    exact this
  have h3 := congrArg (fun m => (Multiset.map (fun z : ℂ => ((f z.re : ℝ) : ℂ)) m).sum) h2
  simp only [Multiset.map_map, Function.comp_def, Complex.ofReal_re] at h3
  exact h3.symm

lemma g73g_vn_spec {n : Type} [Fintype n] [DecidableEq n] {k : ℕ} (M : Matrix n n ℂ)
    (hM : M.IsHermitian) (lam : Fin k → ℝ) (h : HasSpectrum M lam) :
    vnEntropy M = -∑ j, lam j * Real.logb 2 (lam j) := by
  unfold vnEntropy
  rw [g73g_trace_cfc_spec M hM lam h]
  simp

lemma g73g_sq (x : ℝ) (hx : 0 ≤ x) : (Real.sqrt x : ℂ) ^ 2 = (x : ℂ) := by
  rw [← Complex.ofReal_pow, Real.sq_sqrt hx]

lemma g73g_spec2 (M : Matrix (Fin 2) (Fin 2) ℂ) (t : ℝ) (htr : M.trace = 1)
    (hdet : M.det = (((1 - t*t)/4 : ℝ) : ℂ)) : HasSpectrum M ![(1+t)/2, (1-t)/2] := by
  unfold HasSpectrum
  rw [Matrix.charpoly_fin_two, htr, hdet, Fin.prod_univ_two]
  have e1 : (1 : ℂ) = (((1+t)/2 : ℝ) : ℂ) + (((1-t)/2 : ℝ) : ℂ) := by push_cast; ring
  have e2 : (((1 - t*t)/4 : ℝ) : ℂ) = (((1+t)/2 : ℝ) : ℂ) * (((1-t)/2 : ℝ) : ℂ) := by push_cast; ring
  rw [e2]
  conv_lhs => rw [e1]
  simp only [map_add, map_mul, Matrix.cons_val_zero, Matrix.cons_val_one]
  ring

def g73g_R (p theta : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![((1-p+p*(Real.cos theta)^2 : ℝ) : ℂ), ((p*Real.cos theta*Real.sin theta : ℝ) : ℂ);
    ((p*Real.cos theta*Real.sin theta : ℝ) : ℂ), ((p*(Real.sin theta)^2 : ℝ) : ℂ)]

def g73g_M (eta p theta : ℝ) : Matrix (Fin 2 × Fin 2) (Fin 2) ℂ := fun br k =>
  if k = 0 then
    (if br.1 = 0 then (if br.2 = 0 then (Real.sqrt (1-p) : ℂ) else 0)
     else (Real.sqrt eta : ℂ) * (Real.sqrt p : ℂ) *
       (if br.2 = 0 then (Real.cos theta : ℂ) else (Real.sin theta : ℂ)))
  else
    (if br.1 = 0 then (Real.sqrt (1-eta) : ℂ) * (Real.sqrt p : ℂ) *
       (if br.2 = 0 then (Real.cos theta : ℂ) else (Real.sin theta : ℂ)) else 0)

lemma g73g_B (eta p theta phi : ℝ) (heta : eta ∈ Set.Icc (0 : ℝ) 1) (hp : p ∈ Set.Icc (0 : ℝ) 1) :
    dampingJointOutput (adChannel eta) p theta phi =
      conjSuperop (Matrix.kronecker (Matrix.diagonal ![1, Complex.exp (Complex.I * (phi : ℂ))])
        (1 : Matrix (Fin 2) (Fin 2) ℂ)) (g73g_M eta p theta * (g73g_M eta p theta)ᴴ) := by
  obtain ⟨e0, e1⟩ := heta; obtain ⟨p0, p1⟩ := hp
  have h1 := g73g_sq eta e0
  have h2 := g73g_sq (1-eta) (by linarith)
  push_cast at h2
  have h5 := g73g_sq p p0
  have h6 := g73g_sq (1-p) (by linarith)
  push_cast at h6
  have hz0 : Complex.exp (Complex.I * (phi : ℂ)) ≠ 0 := Complex.exp_ne_zero _
  have hz : (starRingEnd ℂ) (Complex.exp (Complex.I * (phi : ℂ))) =
      (Complex.exp (Complex.I * (phi : ℂ)))⁻¹ := by
    rw [← Complex.exp_conj, ← Complex.exp_neg]; simp
  ext ⟨x1, x2⟩ ⟨y1, y2⟩
  fin_cases x1 <;> fin_cases x2 <;> fin_cases y1 <;> fin_cases y2 <;>
  simp [dampingJointOutput, idTensorSuperop, adChannel, krausApply, adKraus,
    pureDensity, inputPurification, Matrix.mul_apply, conjSuperop, Matrix.kronecker_apply,
    Matrix.diagonal_apply, g73g_M, hz,
    Fin.sum_univ_two, Matrix.sum_apply, Matrix.conjTranspose_apply, Fintype.sum_prod_type,
    -Complex.ofReal_cos, -Complex.ofReal_sin]
  all_goals (try field_simp)
  all_goals (try ring_nf at h1 h2 h5 h6 ⊢)
  all_goals (try simp only [h1, h2, h5, h6])
  all_goals (try ring_nf)


lemma g73g_R_spec (p theta : ℝ) (hp : p ∈ Set.Icc (0 : ℝ) 1) :
    HasSpectrum (g73g_R p theta) (adEigenvalues 1 p theta) := by
  obtain ⟨p0, p1⟩ := hp
  have hsc : (Real.sin theta : ℂ)^2 + (Real.cos theta : ℂ)^2 = 1 := by
    exact_mod_cast Real.sin_sq_add_cos_sq theta
  have hdn : 0 ≤ (1-2*1*p)^2 + 4*1*(1-p)*p*(Real.cos theta)^2 := by
    have : 0 ≤ (1-p)*p := mul_nonneg (by linarith) p0
    positivity
  have htt := Real.mul_self_sqrt hdn
  simp only [adEigenvalues]
  apply g73g_spec2
  · simp [Matrix.trace_fin_two, g73g_R, -Complex.ofReal_cos, -Complex.ofReal_sin]
    linear_combination p * hsc
  · rw [Matrix.det_fin_two]
    simp only [g73g_R, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_cons]
    rw [htt]; push_cast
    linear_combination (p*(1-p)) * Complex.sin_sq_add_cos_sq (theta : ℂ)

lemma g73g_tl_phi (eta p theta phi : ℝ)
    (heta : eta ∈ Set.Icc (0 : ℝ) 1) (hp : p ∈ Set.Icc (0 : ℝ) 1) :
    traceLeft (dampingJointOutput (adChannel eta) p theta phi) = g73g_R p theta := by
  obtain ⟨e0, e1⟩ := heta; obtain ⟨p0, p1⟩ := hp
  have h1 := g73g_sq eta e0
  have h2 := g73g_sq (1-eta) (by linarith)
  push_cast at h2
  have h5 := g73g_sq p p0
  have h6 := g73g_sq (1-p) (by linarith)
  push_cast at h6
  have hz0 : Complex.exp (Complex.I * (phi : ℂ)) ≠ 0 := Complex.exp_ne_zero _
  have hz : (starRingEnd ℂ) (Complex.exp (Complex.I * (phi : ℂ))) =
      (Complex.exp (Complex.I * (phi : ℂ)))⁻¹ := by
    rw [← Complex.exp_conj, ← Complex.exp_neg]; simp
  ext i j; fin_cases i <;> fin_cases j <;>
  simp [traceLeft, dampingJointOutput, idTensorSuperop, adChannel, krausApply, adKraus,
    pureDensity, inputPurification, Matrix.mul_apply, g73g_R, hz,
    Fin.sum_univ_two, Matrix.sum_apply, Matrix.conjTranspose_apply,
    -Complex.ofReal_cos, -Complex.ofReal_sin]
  all_goals (try field_simp)
  all_goals (try ring_nf at h1 h2 h5 h6 ⊢)
  all_goals (try simp only [h1, h2, h5, h6])
  all_goals (try ring_nf)

lemma g73g_A (eta p theta : ℝ) (heta : eta ∈ Set.Icc (0 : ℝ) 1) (hp : p ∈ Set.Icc (0 : ℝ) 1) :
    gadBlockMatrix eta 0 p theta = g73g_M eta p theta * (g73g_M eta p theta)ᴴ := by
  obtain ⟨e0, e1⟩ := heta; obtain ⟨p0, p1⟩ := hp
  have h1 := g73g_sq eta e0
  have h2 := g73g_sq (1-eta) (by linarith)
  push_cast at h2
  have h5 := g73g_sq p p0
  have h6 := g73g_sq (1-p) (by linarith)
  push_cast at h6
  have hs : Real.sqrt (eta*(1-p)*p) = Real.sqrt eta * Real.sqrt (1-p) * Real.sqrt p := by
    rw [Real.sqrt_mul (by nlinarith), Real.sqrt_mul e0]
  ext ⟨x1, x2⟩ ⟨y1, y2⟩
  fin_cases x1 <;> fin_cases x2 <;> fin_cases y1 <;> fin_cases y2 <;>
  simp [gadBlockMatrix, g73g_M, hs, Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply,
    -Complex.ofReal_cos, -Complex.ofReal_sin]
  all_goals (try ring_nf at h1 h2 h5 h6 ⊢)
  all_goals (try simp only [h1, h2, h5, h6])
  all_goals (try ring_nf)

lemma g73g_W_unit (phi : ℝ) :
    (Matrix.kronecker (Matrix.diagonal ![1, Complex.exp (Complex.I * (phi : ℂ))])
        (1 : Matrix (Fin 2) (Fin 2) ℂ))ᴴ *
      Matrix.kronecker (Matrix.diagonal ![1, Complex.exp (Complex.I * (phi : ℂ))])
        (1 : Matrix (Fin 2) (Fin 2) ℂ) = 1 := by
  have hz : (starRingEnd ℂ) (Complex.exp (Complex.I * (phi : ℂ))) *
      Complex.exp (Complex.I * (phi : ℂ)) = 1 := by
    rw [← Complex.exp_conj, ← Complex.exp_add]; simp
  have hz' : Complex.exp (Complex.I * (phi : ℂ)) *
      (starRingEnd ℂ) (Complex.exp (Complex.I * (phi : ℂ))) = 1 := by rw [mul_comm]; exact hz
  ext ⟨x1, x2⟩ ⟨y1, y2⟩
  fin_cases x1 <;> fin_cases x2 <;> fin_cases y1 <;> fin_cases y2 <;>
  simp [Matrix.kronecker_apply, Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two,
    Matrix.diagonal_apply, Matrix.one_apply, Matrix.conjTranspose_apply, hz, hz']

lemma g73g_G (eta p theta : ℝ) (heta : eta ∈ Set.Icc (0 : ℝ) 1) (hp : p ∈ Set.Icc (0 : ℝ) 1) :
    HasSpectrum ((g73g_M eta p theta)ᴴ * g73g_M eta p theta) (adEigenvalues (1-eta) p theta) := by
  obtain ⟨e0, e1⟩ := heta; obtain ⟨p0, p1⟩ := hp
  have h1 := g73g_sq eta e0
  have h2 := g73g_sq (1-eta) (by linarith)
  push_cast at h2
  have h5 := g73g_sq p p0
  have h6 := g73g_sq (1-p) (by linarith)
  push_cast at h6
  have hs2 : (Real.sin theta : ℂ)^2 = 1 - (Real.cos theta : ℂ)^2 := by
    have : (Real.sin theta : ℂ)^2 + (Real.cos theta : ℂ)^2 = 1 := by
      exact_mod_cast Real.sin_sq_add_cos_sq theta
    linear_combination this
  have hdn : 0 ≤ (1-2*(1-eta)*p)^2 + 4*(1-eta)*(1-p)*p*(Real.cos theta)^2 := by
    have : 0 ≤ (1-eta)*(1-p)*p := mul_nonneg (mul_nonneg (by linarith) (by linarith)) p0
    positivity
  have htt := Real.mul_self_sqrt hdn
  simp only [adEigenvalues]
  apply g73g_spec2
  · rw [Matrix.trace_fin_two]
    simp [g73g_M, Matrix.mul_apply, Fin.sum_univ_two, Fintype.sum_prod_type,
      Matrix.conjTranspose_apply, -Complex.ofReal_cos, -Complex.ofReal_sin]
    ring_nf at h1 h2 h5 h6 hs2 ⊢
    simp only [h1, h2, h5, h6, hs2]
    ring_nf
  · rw [Matrix.det_fin_two, htt]
    have h5' : (Real.sqrt p : ℂ)^4 = (p:ℂ)^2 := by rw [show (4:ℕ) = 2*2 by rfl, pow_mul, h5]
    have h6' : (Real.sqrt (1-p) : ℂ)^4 = (1-(p:ℂ))^2 := by rw [show (4:ℕ) = 2*2 by rfl, pow_mul, h6]
    have h1' : (Real.sqrt eta : ℂ)^4 = (eta:ℂ)^2 := by rw [show (4:ℕ) = 2*2 by rfl, pow_mul, h1]
    have h2' : (Real.sqrt (1-eta) : ℂ)^4 = (1-(eta:ℂ))^2 := by
      rw [show (4:ℕ) = 2*2 by rfl, pow_mul, h2]
    have hs4 : (Real.sin theta : ℂ)^4 = (1 - (Real.cos theta : ℂ)^2)^2 := by
      rw [show (4:ℕ) = 2*2 by rfl, pow_mul, hs2]
    simp [g73g_M, Matrix.mul_apply, Fin.sum_univ_two, Fintype.sum_prod_type,
      Matrix.conjTranspose_apply, -Complex.ofReal_cos, -Complex.ofReal_sin]
    ring_nf at h1 h2 h5 h6 hs2 h1' h2' h5' h6' hs4 ⊢
    simp only [h1, h2, h5, h6, hs2, h1', h2', h5', h6', hs4]
    ring_nf

lemma g73g_U_unit (phi : ℝ) :
    (Matrix.diagonal ![1, Complex.exp (Complex.I * (phi : ℂ))])ᴴ *
      Matrix.diagonal ![1, Complex.exp (Complex.I * (phi : ℂ))] = 1 := by
  have hz : (starRingEnd ℂ) (Complex.exp (Complex.I * (phi : ℂ))) *
      Complex.exp (Complex.I * (phi : ℂ)) = 1 := by
    rw [← Complex.exp_conj, ← Complex.exp_add]; simp
  ext i j; fin_cases i <;> fin_cases j <;>
  simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.diagonal_apply, Matrix.conjTranspose_apply, hz]

lemma g73g_cp_conj {n : Type} [Fintype n] [DecidableEq n] (W X : Matrix n n ℂ) (hW : Wᴴ * W = 1) :
    (conjSuperop W X).charpoly = X.charpoly := by
  unfold conjSuperop
  rw [Matrix.charpoly_mul_comm, ← Matrix.mul_assoc, hW, Matrix.one_mul]

lemma g73g_tr_conj (phi : ℝ) (X : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) :
    traceRight (conjSuperop (Matrix.kronecker (Matrix.diagonal ![1, Complex.exp (Complex.I * (phi : ℂ))])
        (1 : Matrix (Fin 2) (Fin 2) ℂ)) X) =
      conjSuperop (Matrix.diagonal ![1, Complex.exp (Complex.I * (phi : ℂ))]) (traceRight X) := by
  ext i j; fin_cases i <;> fin_cases j <;>
  simp [traceRight, conjSuperop, Matrix.kronecker_apply, Matrix.mul_apply, Fintype.sum_prod_type,
    Fin.sum_univ_two, Matrix.diagonal_apply, Matrix.one_apply, Matrix.conjTranspose_apply] <;> ring

def g73g_Bob (eta p theta : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![((1-eta*p : ℝ) : ℂ), ((Real.sqrt (eta*(1-p)*p)*Real.cos theta : ℝ) : ℂ);
    ((Real.sqrt (eta*(1-p)*p)*Real.cos theta : ℝ) : ℂ), ((eta*p : ℝ) : ℂ)]

lemma g73g_trMM (eta p theta : ℝ) (heta : eta ∈ Set.Icc (0 : ℝ) 1) (hp : p ∈ Set.Icc (0 : ℝ) 1) :
    traceRight (g73g_M eta p theta * (g73g_M eta p theta)ᴴ) = g73g_Bob eta p theta := by
  obtain ⟨e0, e1⟩ := heta; obtain ⟨p0, p1⟩ := hp
  have h1 := g73g_sq eta e0
  have h2 := g73g_sq (1-eta) (by linarith)
  push_cast at h2
  have h5 := g73g_sq p p0
  have h6 := g73g_sq (1-p) (by linarith)
  push_cast at h6
  have hs2 : (Real.sin theta : ℂ)^2 = 1 - (Real.cos theta : ℂ)^2 := by
    have : (Real.sin theta : ℂ)^2 + (Real.cos theta : ℂ)^2 = 1 := by
      exact_mod_cast Real.sin_sq_add_cos_sq theta
    linear_combination this
  have hs : Real.sqrt (eta*(1-p)*p) = Real.sqrt eta * Real.sqrt (1-p) * Real.sqrt p := by
    rw [Real.sqrt_mul (by nlinarith), Real.sqrt_mul e0]
  ext i j; fin_cases i <;> fin_cases j <;>
  simp [traceRight, g73g_Bob, g73g_M, hs, Matrix.mul_apply, Fin.sum_univ_two,
    Matrix.conjTranspose_apply, Fintype.sum_prod_type, -Complex.ofReal_cos, -Complex.ofReal_sin]
  all_goals (try ring_nf at h1 h2 h5 h6 hs2 ⊢)
  all_goals (try simp only [h1, h2, h5, h6, hs2])
  all_goals (try ring_nf)

lemma g73g_Bob_spec (eta p theta : ℝ) (heta : eta ∈ Set.Icc (0 : ℝ) 1) (hp : p ∈ Set.Icc (0 : ℝ) 1) :
    HasSpectrum (g73g_Bob eta p theta) (adEigenvalues eta p theta) := by
  obtain ⟨e0, e1⟩ := heta; obtain ⟨p0, p1⟩ := hp
  have hdn : 0 ≤ (1-2*eta*p)^2 + 4*eta*(1-p)*p*(Real.cos theta)^2 := by
    have : 0 ≤ eta*(1-p)*p := mul_nonneg (mul_nonneg e0 (by linarith)) p0
    positivity
  have htt := Real.mul_self_sqrt hdn
  have hq : Real.sqrt (eta*(1-p)*p) ^ 2 = eta*(1-p)*p :=
    Real.sq_sqrt (mul_nonneg (mul_nonneg e0 (by linarith)) p0)
  simp only [adEigenvalues]
  apply g73g_spec2
  · simp [Matrix.trace_fin_two, g73g_Bob]
  · rw [Matrix.det_fin_two]
    simp only [g73g_Bob, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_cons]
    rw [htt]
    have : (1-eta*p) * (eta*p) -
        (Real.sqrt (eta*(1-p)*p)*Real.cos theta) * (Real.sqrt (eta*(1-p)*p)*Real.cos theta) =
        (1 - ((1-2*eta*p)^2 + 4*eta*(1-p)*p*(Real.cos theta)^2))/4 := by
      linear_combination (-(Real.cos theta)^2) * hq
    rw [← this]; push_cast; ring

lemma g73g_joint_spec (eta p theta phi : ℝ) (heta : eta ∈ Set.Icc (0 : ℝ) 1)
    (hp : p ∈ Set.Icc (0 : ℝ) 1) :
    HasSpectrum (dampingJointOutput (adChannel eta) p theta phi) (adJointEigenvalues eta p theta) := by
  have hG := g73g_G eta p theta heta hp
  unfold HasSpectrum at hG ⊢
  rw [g73g_B eta p theta phi heta hp, g73g_cp_conj _ _ (g73g_W_unit phi),
    Matrix.charpoly_mul_comm_of_le _ _ (by simp), hG]
  simp only [Fin.prod_univ_two, Fin.prod_univ_four, adJointEigenvalues]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.head_cons, Matrix.tail_cons, Complex.ofReal_zero, map_zero, sub_zero]
  simp
  ring

lemma g73g_joint_herm (eta p theta phi : ℝ) (heta : eta ∈ Set.Icc (0 : ℝ) 1)
    (hp : p ∈ Set.Icc (0 : ℝ) 1) :
    (dampingJointOutput (adChannel eta) p theta phi).IsHermitian := by
  rw [g73g_B eta p theta phi heta hp]
  unfold conjSuperop
  set W := Matrix.kronecker (Matrix.diagonal ![1, Complex.exp (Complex.I * (phi : ℂ))])
        (1 : Matrix (Fin 2) (Fin 2) ℂ)
  have : W * (g73g_M eta p theta * (g73g_M eta p theta)ᴴ) * Wᴴ =
      (W * g73g_M eta p theta) * (W * g73g_M eta p theta)ᴴ := by
    rw [Matrix.conjTranspose_mul]; simp only [Matrix.mul_assoc]
  rw [this]
  exact Matrix.isHermitian_mul_conjTranspose_self _

lemma g73g_norm (p theta phi : ℝ) (hp : p ∈ Set.Icc (0 : ℝ) 1) :
    ‖inputPurification p theta phi‖ = 1 := by
  obtain ⟨p0, p1⟩ := hp
  rw [EuclideanSpace.norm_eq, Real.sqrt_eq_one]
  have hn : ‖Complex.exp (Complex.I * (phi : ℂ))‖ = 1 := by
    rw [mul_comm]; exact Complex.norm_exp_ofReal_mul_I phi
  simp [inputPurification, Fintype.sum_prod_type, Fin.sum_univ_two, hn, Complex.norm_real,
    -Complex.ofReal_cos, -Complex.ofReal_sin, mul_pow, Real.sq_sqrt p0, Real.sq_sqrt (sub_nonneg.2 p1)]
  linear_combination p * Real.sin_sq_add_cos_sq theta

lemma g73g_gi (p theta phi : ℝ) (hp : p ∈ Set.Icc (0 : ℝ) 1) :
    generalInput p theta phi =
      !![((1-p : ℝ) : ℂ), (Real.sqrt ((1-p)*p) : ℂ) *
          Complex.exp (-Complex.I * (phi : ℂ)) * (Real.cos theta : ℂ);
        (Real.sqrt ((1-p)*p) : ℂ) *
          Complex.exp (Complex.I * (phi : ℂ)) * (Real.cos theta : ℂ), (p : ℂ)] := by
  obtain ⟨p0, p1⟩ := hp
  have h5 := g73g_sq p p0
  have h6 := g73g_sq (1-p) (by linarith)
  push_cast at h6
  have hs2 : (Real.sin theta : ℂ)^2 = 1 - (Real.cos theta : ℂ)^2 := by
    have : (Real.sin theta : ℂ)^2 + (Real.cos theta : ℂ)^2 = 1 := by
      exact_mod_cast Real.sin_sq_add_cos_sq theta
    linear_combination this
  have hs : Real.sqrt ((1-p)*p) = Real.sqrt (1-p) * Real.sqrt p := Real.sqrt_mul (by linarith) p
  have hz0 : Complex.exp (Complex.I * (phi : ℂ)) ≠ 0 := Complex.exp_ne_zero _
  have hz : (starRingEnd ℂ) (Complex.exp (Complex.I * (phi : ℂ))) =
      (Complex.exp (Complex.I * (phi : ℂ)))⁻¹ := by
    rw [← Complex.exp_conj, ← Complex.exp_neg]; simp
  have hneg : Complex.exp (-Complex.I * (phi : ℂ)) = (Complex.exp (Complex.I * (phi : ℂ)))⁻¹ := by
    rw [← Complex.exp_neg]; ring_nf
  ext i j; fin_cases i <;> fin_cases j <;>
  simp [generalInput, traceLeft, pureDensity, inputPurification, Fin.sum_univ_two, hz, hneg, hs, Complex.exp_neg,
    -Complex.ofReal_cos, -Complex.ofReal_sin]
  all_goals (try field_simp)
  all_goals (try ring_nf at h5 h6 hs2 ⊢)
  all_goals (try simp only [h5, h6, hs2])
  all_goals (try ring_nf)

theorem g73g_adGen (eta p theta phi : ℝ)
    (heta : eta ∈ Set.Icc (0 : ℝ) 1) (hp : p ∈ Set.Icc (0 : ℝ) 1)
    (htheta : theta ∈ Set.Icc (0 : ℝ) Real.pi) :
    ‖inputPurification p theta phi‖ = 1 ∧
    generalInput p theta phi =
      !![((1-p : ℝ) : ℂ), (Real.sqrt ((1-p)*p) : ℂ) *
          Complex.exp (-Complex.I * (phi : ℂ)) * (Real.cos theta : ℂ);
        (Real.sqrt ((1-p)*p) : ℂ) *
          Complex.exp (Complex.I * (phi : ℂ)) * (Real.cos theta : ℂ), (p : ℂ)] ∧
    (let U : Matrix (Fin 2) (Fin 2) ℂ := Matrix.diagonal
       ![1, Complex.exp (Complex.I * (phi : ℂ))]
     dampingJointOutput (adChannel eta) p theta phi =
       conjSuperop (Matrix.kronecker U (1 : Matrix (Fin 2) (Fin 2) ℂ))
         (gadBlockMatrix eta 0 p theta)) ∧
    vnEntropy (dampingJointOutput (adChannel eta) p theta phi) =
      vnEntropy (dampingJointOutput (adChannel eta) p theta 0) ∧
    HasSpectrum (traceLeft (dampingJointOutput (adChannel eta) p theta phi))
      (adEigenvalues 1 p theta) ∧
    HasSpectrum (dampingJointOutput (adChannel eta) p theta phi) (adJointEigenvalues eta p theta) ∧
    traceRight (dampingJointOutput (adChannel eta) p theta 0) =
      !![((1-eta*p : ℝ) : ℂ), ((Real.sqrt (eta*(1-p)*p)*Real.cos theta : ℝ) : ℂ);
        ((Real.sqrt (eta*(1-p)*p)*Real.cos theta : ℝ) : ℂ), ((eta*p : ℝ) : ℂ)] ∧
    HasSpectrum (traceRight (dampingJointOutput (adChannel eta) p theta phi))
      (adEigenvalues eta p theta) := by
  refine ⟨g73g_norm p theta phi hp, g73g_gi p theta phi hp, ?_, ?_, ?_,
    g73g_joint_spec eta p theta phi heta hp, ?_, ?_⟩
  · dsimp only
    rw [g73g_A eta p theta heta hp]
    exact g73g_B eta p theta phi heta hp
  · rw [g73g_vn_spec _ (g73g_joint_herm eta p theta phi heta hp) _
        (g73g_joint_spec eta p theta phi heta hp),
      g73g_vn_spec _ (g73g_joint_herm eta p theta 0 heta hp) _
        (g73g_joint_spec eta p theta 0 heta hp)]
  · rw [g73g_tl_phi eta p theta phi heta hp]
    exact g73g_R_spec p theta hp
  · rw [g73g_B eta p theta 0 heta hp, g73g_tr_conj, g73g_trMM eta p theta heta hp]
    show _ = g73g_Bob eta p theta
    ext i j; fin_cases i <;> fin_cases j <;>
    simp [conjSuperop, Matrix.mul_apply, Fin.sum_univ_two, Matrix.diagonal_apply,
      Matrix.conjTranspose_apply]
  · unfold HasSpectrum
    rw [g73g_B eta p theta phi heta hp, g73g_tr_conj, g73g_cp_conj _ _ (g73g_U_unit phi),
      g73g_trMM eta p theta heta hp]
    exact g73g_Bob_spec eta p theta heta hp



/-- PDF pp.4–5, Eqs.(14)–(21): normalized constructed AD input/output, corrected
positive phase unitary, phase-invariant joint entropy, and all marginal spectra.
Displayed joint coordinates are Bob first, as in (16). -/
theorem solution (eta p theta phi : ℝ)
    (heta : eta ∈ Set.Icc (0 : ℝ) 1) (hp : p ∈ Set.Icc (0 : ℝ) 1)
    (htheta : theta ∈ Set.Icc (0 : ℝ) Real.pi) :
    ‖inputPurification p theta phi‖ = 1 ∧
    generalInput p theta phi =
      !![((1-p : ℝ) : ℂ), (Real.sqrt ((1-p)*p) : ℂ) *
          Complex.exp (-Complex.I * (phi : ℂ)) * (Real.cos theta : ℂ);
        (Real.sqrt ((1-p)*p) : ℂ) *
          Complex.exp (Complex.I * (phi : ℂ)) * (Real.cos theta : ℂ), (p : ℂ)] ∧
    (let U : Matrix (Fin 2) (Fin 2) ℂ := Matrix.diagonal
       ![1, Complex.exp (Complex.I * (phi : ℂ))]
     dampingJointOutput (adChannel eta) p theta phi =
       conjSuperop (Matrix.kronecker U (1 : Matrix (Fin 2) (Fin 2) ℂ))
         (gadBlockMatrix eta 0 p theta)) ∧
    vnEntropy (dampingJointOutput (adChannel eta) p theta phi) =
      vnEntropy (dampingJointOutput (adChannel eta) p theta 0) ∧
    HasSpectrum (traceLeft (dampingJointOutput (adChannel eta) p theta phi))
      (adEigenvalues 1 p theta) ∧
    HasSpectrum (dampingJointOutput (adChannel eta) p theta phi) (adJointEigenvalues eta p theta) ∧
    traceRight (dampingJointOutput (adChannel eta) p theta 0) =
      !![((1-eta*p : ℝ) : ℂ), ((Real.sqrt (eta*(1-p)*p)*Real.cos theta : ℝ) : ℂ);
        ((Real.sqrt (eta*(1-p)*p)*Real.cos theta : ℝ) : ℂ), ((eta*p : ℝ) : ℂ)] ∧
    HasSpectrum (traceRight (dampingJointOutput (adChannel eta) p theta phi))
      (adEigenvalues eta p theta) := by
  exact g73g_adGen eta p theta phi heta hp htheta


end
