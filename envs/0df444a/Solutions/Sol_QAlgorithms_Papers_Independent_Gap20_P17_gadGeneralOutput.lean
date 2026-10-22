-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Gap20.P17.gadGeneralOutput
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T21:51:43.456552+00:00
-- url     : https://prove2.me/submissions/fc7aca5f-69d4-439e-8057-4958f821b693

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

lemma g73g_ad_apply (eta : ℝ) (X : Matrix (Fin 2) (Fin 2) ℂ) :
    adChannel eta X = !![X 0 0 + (Real.sqrt (1-eta) : ℂ) * (Real.sqrt (1-eta) : ℂ) * X 1 1,
      (Real.sqrt eta : ℂ) * X 0 1; (Real.sqrt eta : ℂ) * X 1 0,
      (Real.sqrt eta : ℂ) * (Real.sqrt eta : ℂ) * X 1 1] := by
  ext i j; fin_cases i <;> fin_cases j <;>
  simp [adChannel, krausApply, adKraus, Matrix.mul_apply, Fin.sum_univ_two, Matrix.sum_apply,
    Matrix.conjTranspose_apply] <;> ring

lemma g73g_recv (eta : ℝ) (X : Matrix (Fin 2) (Fin 2) ℂ) :
    receiverChannel (adDilation eta) X = adChannel eta X := by
  rw [g73g_ad_apply]
  ext i j; fin_cases i <;> fin_cases j <;>
  simp [receiverChannel, traceRight, adDilation, adKraus, Matrix.mul_apply, Fin.sum_univ_two,
    Fintype.sum_prod_type, Matrix.conjTranspose_apply] <;> ring

lemma g73g_comp (eta : ℝ) (X : Matrix (Fin 2) (Fin 2) ℂ) :
    complementaryChannel (adDilation eta) X = !![X 0 0 + (Real.sqrt eta : ℂ) * (Real.sqrt eta : ℂ) * X 1 1,
      (Real.sqrt (1-eta) : ℂ) * X 0 1; (Real.sqrt (1-eta) : ℂ) * X 1 0,
      (Real.sqrt (1-eta) : ℂ) * (Real.sqrt (1-eta) : ℂ) * X 1 1] := by
  ext i j; fin_cases i <;> fin_cases j <;>
  simp [complementaryChannel, traceLeft, adDilation, adKraus, Matrix.mul_apply, Fin.sum_univ_two,
    Fintype.sum_prod_type, Matrix.conjTranspose_apply] <;> ring

lemma g73g_sqC (x : ℝ) (hx : 0 ≤ x) : (Real.sqrt x : ℂ) * (Real.sqrt x : ℂ) = (x : ℂ) := by
  rw [← Complex.ofReal_mul, Real.mul_self_sqrt hx]

lemma g73g_kraus (eta : ℝ) (h0 : 0 ≤ eta) (h1 : eta ≤ 1) : IsKrausFamily (adKraus eta) := by
  have a := g73g_sqC eta h0
  have b := g73g_sqC (1-eta) (by linarith)
  push_cast at b
  unfold IsKrausFamily
  ext i j; fin_cases i <;> fin_cases j <;>
  simp [adKraus, Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply, Matrix.one_apply]
  linear_combination a + b

lemma g73g_iso (eta : ℝ) (h0 : 0 ≤ eta) (h1 : eta ≤ 1) : IsIsometry (adDilation eta) := by
  have a := g73g_sqC eta h0
  have b := g73g_sqC (1-eta) (by linarith)
  push_cast at b
  unfold IsIsometry
  ext i j; fin_cases i <;> fin_cases j <;>
  simp [adDilation, adKraus, Matrix.mul_apply, Fin.sum_univ_two, Fintype.sum_prod_type,
    Matrix.conjTranspose_apply, Matrix.one_apply]
  linear_combination a + b

lemma g73g_isChan (eta : ℝ) (h0 : 0 ≤ eta) (h1 : eta ≤ 1) : IsChannel (adChannel eta) :=
  ⟨2, adKraus eta, g73g_kraus eta h0 h1, fun _ => rfl⟩

theorem g73g_degr (eta : ℝ) (heta : eta ∈ Set.Icc (0 : ℝ) 1) :
    (1/2 ≤ eta → IsDegradable (adDilation eta)) ∧
    (eta ≤ 1/2 → IsAntidegradable (adDilation eta)) := by
  obtain ⟨h0, h1⟩ := heta
  have a := g73g_sqC eta h0
  have b := g73g_sqC (1-eta) (by linarith)
  push_cast at a b
  constructor
  · intro h
    have hpos : 0 < eta := by linarith
    set q := (1-eta)/eta with hq
    have q0 : 0 ≤ q := div_nonneg (by linarith) hpos.le
    have q1 : q ≤ 1 := by rw [hq, div_le_one hpos]; linarith
    have c := g73g_sqC q q0
    have d := g73g_sqC (1-q) (by linarith)
    have e : (Real.sqrt q : ℂ) * (Real.sqrt eta : ℂ) = (Real.sqrt (1-eta) : ℂ) := by
      rw [← Complex.ofReal_mul, ← Real.sqrt_mul q0, hq, div_mul_cancel₀ _ hpos.ne']
    have f : (q : ℂ) * eta = 1 - eta := by
      rw [hq]; push_cast; field_simp [show (eta:ℂ) ≠ 0 by exact_mod_cast hpos.ne']
    push_cast at d
    refine ⟨g73g_iso eta h0 h1, adChannel q, g73g_isChan q q0 q1, fun X => ?_⟩
    rw [g73g_recv, g73g_comp, g73g_ad_apply, g73g_ad_apply]
    ext i j; fin_cases i <;> fin_cases j <;> simp
    · rw [a, b, d]; linear_combination (X 1 1) * f
    · rw [← e]; ring
    · rw [← e]; ring
    · rw [a, c, b]; linear_combination (-(X 1 1)) * f
  · intro h
    have hpos : 0 < 1 - eta := by linarith
    set q := eta/(1-eta) with hq
    have q0 : 0 ≤ q := div_nonneg h0 hpos.le
    have q1 : q ≤ 1 := by rw [hq, div_le_one hpos]; linarith
    have c := g73g_sqC q q0
    have d := g73g_sqC (1-q) (by linarith)
    have e : (Real.sqrt q : ℂ) * (Real.sqrt (1-eta) : ℂ) = (Real.sqrt eta : ℂ) := by
      rw [← Complex.ofReal_mul, ← Real.sqrt_mul q0, hq, div_mul_cancel₀ _ hpos.ne']
    have f : (q : ℂ) * (1 - eta) = eta := by
      rw [hq]; push_cast; field_simp [show (1 - (eta:ℂ)) ≠ 0 by exact_mod_cast hpos.ne']
    push_cast at d
    refine ⟨g73g_iso eta h0 h1, adChannel q, g73g_isChan q q0 q1, fun X => ?_⟩
    rw [g73g_recv, g73g_comp, g73g_ad_apply, g73g_ad_apply]
    ext i j; fin_cases i <;> fin_cases j <;> simp
    · rw [a, b, d]; linear_combination (X 1 1) * f
    · rw [← e]; ring
    · rw [← e]; ring
    · rw [c, b, a]; linear_combination (-(X 1 1)) * f
lemma g73g_cfc_trace {n : Type*} [Fintype n] [DecidableEq n] {Y : Matrix n n ℂ} (hY : Y.IsHermitian)
    (f : ℝ → ℝ) : (cfc f Y).trace = ∑ i, ((f (hY.eigenvalues i) : ℝ) : ℂ) := by
  rw [hY.cfc_eq f, Matrix.IsHermitian.cfc, Unitary.conjStarAlgAut_apply, Matrix.trace_mul_cycle,
    Unitary.star_mul_self_of_mem hY.eigenvectorUnitary.2, one_mul, Matrix.trace_diagonal]
  rfl

lemma g73g_diag_herm {n : Type*} [Fintype n] [DecidableEq n] (d : n → ℝ) :
    (Matrix.diagonal (fun i => (d i : ℂ))).IsHermitian := by
  rw [Matrix.IsHermitian, Matrix.diagonal_conjTranspose]
  congr 1; funext i; simp

lemma g73g_trace_cfc_diag {n : Type*} [Fintype n] [DecidableEq n] (d : n → ℝ) (f : ℝ → ℝ) :
    (cfc f (Matrix.diagonal (fun i => (d i : ℂ)))).trace = ∑ i, ((f (d i) : ℝ) : ℂ) := by
  have hD := g73g_diag_herm d
  rw [g73g_cfc_trace hD]
  have h1 := hD.roots_charpoly_eq_eigenvalues
  rw [Matrix.charpoly_diagonal, Polynomial.roots_prod _ _ (by
    simp [Finset.prod_ne_zero_iff, Polynomial.X_sub_C_ne_zero])] at h1
  simp only [Polynomial.roots_X_sub_C] at h1
  have h2 : Multiset.map (fun i => (d i : ℂ)) Finset.univ.val =
      Multiset.map (fun i => ((hD.eigenvalues i : ℝ) : ℂ)) Finset.univ.val := by
    have := h1
    rw [Multiset.bind_singleton] at this
    exact this
  have h3 := congrArg (fun m => (Multiset.map (fun z : ℂ => ((f z.re : ℝ) : ℂ)) m).sum) h2
  simp only [Multiset.map_map, Function.comp_def, Complex.ofReal_re] at h3
  exact h3.symm

lemma g73g_vn_diag {n : Type*} [Fintype n] [DecidableEq n] (d : n → ℝ) :
    vnEntropy (Matrix.diagonal (fun i => (d i : ℂ))) = -∑ i, d i * Real.logb 2 (d i) := by
  unfold vnEntropy
  rw [g73g_trace_cfc_diag]
  simp

lemma g73g_diag_eq (q : ℝ) : diagonalInput q = Matrix.diagonal (fun i => ((![1-q, q] : Fin 2 → ℝ) i : ℂ)) := by
  unfold diagonalInput; congr 1; funext i; fin_cases i <;> simp

lemma g73g_vn_diagInput (q : ℝ) : vnEntropy (diagonalInput q) = binEntropy2 q := by
  rw [g73g_diag_eq, g73g_vn_diag]
  simp [Fin.sum_univ_two, binEntropy2, Real.binEntropy, Real.logb, Real.log_inv]
  ring

lemma g73g_ad_diag (eta p : ℝ) (h0 : 0 ≤ eta) (h1 : eta ≤ 1) :
    adChannel eta (diagonalInput p) = diagonalInput (eta*p) := by
  have a := g73g_sqC eta h0
  have b := g73g_sqC (1-eta) (by linarith)
  push_cast at b
  rw [g73g_ad_apply]
  ext i j; fin_cases i <;> fin_cases j <;> simp [diagonalInput, a, b] <;> ring

lemma g73g_comp_diag (eta p : ℝ) (h0 : 0 ≤ eta) (h1 : eta ≤ 1) :
    complementaryChannel (adDilation eta) (diagonalInput p) = diagonalInput ((1-eta)*p) := by
  have a := g73g_sqC eta h0
  have b := g73g_sqC (1-eta) (by linarith)
  push_cast at b
  rw [g73g_comp]
  ext i j; fin_cases i <;> fin_cases j <;> simp [diagonalInput, a, b] <;> ring

theorem g73g_adEnt (eta p : ℝ) (heta : eta ∈ Set.Icc (0 : ℝ) 1)
    (hp : p ∈ Set.Icc (0 : ℝ) 1) :
    adChannel eta (diagonalInput p) = diagonalInput (eta*p) ∧
    forwardInfo (adDilation eta) (diagonalInput p) =
      binEntropy2 (eta*p) - binEntropy2 ((1-eta)*p) ∧
    reverseInfo (adDilation eta) (diagonalInput p) =
      binEntropy2 p - binEntropy2 ((1-eta)*p) := by
  obtain ⟨h0, h1⟩ := heta
  refine ⟨g73g_ad_diag eta p h0 h1, ?_, ?_⟩
  · unfold forwardInfo
    rw [g73g_recv, g73g_ad_diag eta p h0 h1, g73g_comp_diag eta p h0 h1, g73g_vn_diagInput,
      g73g_vn_diagInput]
  · unfold reverseInfo
    rw [g73g_comp_diag eta p h0 h1, g73g_vn_diagInput, g73g_vn_diagInput]
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

def g73g_e : Fin 2 ⊕ Fin 2 ≃ Fin 2 × Fin 2 where
  toFun := fun s => match s with
    | Sum.inl i => (i, i)
    | Sum.inr i => (i, 1 - i)
  invFun := fun x => if x.1 = x.2 then Sum.inl x.1 else Sum.inr x.1
  left_inv := by decide
  right_inv := by decide

def g73g_J (a c d u v : ℝ) : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  Matrix.reindex g73g_e g73g_e
    (Matrix.fromBlocks !![(a:ℂ), (c:ℂ); (c:ℂ), (d:ℂ)] 0 0 !![(v:ℂ), 0; 0, (u:ℂ)])

lemma g73g_J_cp (a c d u v : ℝ) : (g73g_J a c d u v).charpoly =
    (Polynomial.X ^ 2 - Polynomial.C ((a:ℂ) + d) * Polynomial.X + Polynomial.C ((a:ℂ)*d - c*c)) *
    (Polynomial.X ^ 2 - Polynomial.C ((v:ℂ) + u) * Polynomial.X + Polynomial.C ((v:ℂ)*u)) := by
  rw [g73g_J, Matrix.charpoly_reindex, Matrix.charpoly_fromBlocks_zero₁₂,
    Matrix.charpoly_fin_two, Matrix.charpoly_fin_two]
  simp [Matrix.trace_fin_two, Matrix.det_fin_two]

lemma g73g_J_herm (a c d u v : ℝ) : (g73g_J a c d u v).IsHermitian := by
  rw [g73g_J, Matrix.reindex_apply]
  refine Matrix.IsHermitian.submatrix (Matrix.IsHermitian.fromBlocks ?_ (by simp) ?_) _ <;>
  · ext i j; fin_cases i <;> fin_cases j <;> simp

lemma g73g_J_apply (a c d u v : ℝ) (x y : Fin 2 × Fin 2) : g73g_J a c d u v x y =
    if x = (0,0) ∧ y = (0,0) then (a:ℂ) else if x = (0,0) ∧ y = (1,1) then (c:ℂ)
    else if x = (1,1) ∧ y = (0,0) then (c:ℂ) else if x = (1,1) ∧ y = (1,1) then (d:ℂ)
    else if x = (0,1) ∧ y = (0,1) then (v:ℂ) else if x = (1,0) ∧ y = (1,0) then (u:ℂ) else 0 := by
  obtain ⟨x1, x2⟩ := x; obtain ⟨y1, y2⟩ := y
  fin_cases x1 <;> fin_cases x2 <;> fin_cases y1 <;> fin_cases y2 <;> rfl

lemma g73g_sq (x : ℝ) (hx : 0 ≤ x) : (Real.sqrt x : ℂ) ^ 2 = (x : ℂ) := by
  rw [← Complex.ofReal_pow, Real.sq_sqrt hx]

lemma g73g_gad_diag (eta alpha p : ℝ)
    (heta : eta ∈ Set.Icc (0 : ℝ) 1) (halpha : alpha ∈ Set.Icc (0 : ℝ) 1) :
    gadChannel eta alpha (diagonalInput p) = diagonalInput (eta*p+(1-eta)*alpha) := by
  obtain ⟨e0, e1⟩ := heta; obtain ⟨a0, a1⟩ := halpha
  have h1 := g73g_sq eta e0
  have h2 := g73g_sq (1-eta) (by linarith)
  push_cast at h2
  have h3 := g73g_sq alpha a0
  have h4 := g73g_sq (1-alpha) (by linarith)
  push_cast at h4
  ext i j; fin_cases i <;> fin_cases j <;>
  simp [gadChannel, krausApply, gadKraus, adKraus, diagonalInput, Matrix.mul_apply,
    Fin.sum_univ_four, Fin.sum_univ_two, Matrix.sum_apply, Matrix.conjTranspose_apply]
  all_goals (try ring_nf at h1 h2 h3 h4 ⊢)
  all_goals (try simp only [h1, h2, h3, h4])
  all_goals (try ring_nf)

lemma g73g_joint_diag (eta alpha p : ℝ)
    (heta : eta ∈ Set.Icc (0 : ℝ) 1) (halpha : alpha ∈ Set.Icc (0 : ℝ) 1)
    (hp : p ∈ Set.Icc (0 : ℝ) 1) :
    dampingJointOutput (gadChannel eta alpha) p (Real.pi/2) 0 =
      g73g_J ((1-alpha)*(1-p)+alpha*eta*(1-p)) (Real.sqrt eta * Real.sqrt (1-p) * Real.sqrt p)
        ((1-alpha)*p*eta+alpha*p) (alpha*(1-eta)*(1-p)) ((1-alpha)*(1-eta)*p) := by
  obtain ⟨e0, e1⟩ := heta; obtain ⟨a0, a1⟩ := halpha; obtain ⟨p0, p1⟩ := hp
  have h1 := g73g_sq eta e0
  have h2 := g73g_sq (1-eta) (by linarith)
  push_cast at h2
  have h3 := g73g_sq alpha a0
  have h4 := g73g_sq (1-alpha) (by linarith)
  push_cast at h4
  have h5 := g73g_sq p p0
  have h6 := g73g_sq (1-p) (by linarith)
  push_cast at h6
  ext ⟨x1, x2⟩ ⟨y1, y2⟩
  rw [g73g_J_apply]
  fin_cases x1 <;> fin_cases x2 <;> fin_cases y1 <;> fin_cases y2 <;>
  simp [dampingJointOutput, idTensorSuperop, gadChannel, krausApply, gadKraus, adKraus,
    pureDensity, inputPurification, Matrix.mul_apply,
    Fin.sum_univ_four, Fin.sum_univ_two, Matrix.sum_apply, Matrix.conjTranspose_apply]
  all_goals (try ring_nf at h1 h2 h3 h4 h5 h6 ⊢)
  all_goals (try simp only [h1, h2, h3, h4, h5, h6])
  all_goals (try ring_nf)


theorem g73g_gadDiag (eta alpha p : ℝ)
    (heta : eta ∈ Set.Icc (0 : ℝ) 1) (halpha : alpha ∈ Set.Icc (0 : ℝ) 1)
    (hp : p ∈ Set.Icc (0 : ℝ) 1) :
    gadChannel eta alpha (diagonalInput p) = diagonalInput (eta*p+(1-eta)*alpha) ∧
    vnEntropy (gadChannel eta alpha (diagonalInput p)) = binEntropy2 (eta*p+(1-eta)*alpha) ∧
    HasSpectrum (dampingJointOutput (gadChannel eta alpha) p (Real.pi/2) 0)
      (gadDiagonalEigenvalues eta alpha p) ∧
    vnEntropy (dampingJointOutput (gadChannel eta alpha) p (Real.pi/2) 0) =
      entropy4 (gadDiagonalEigenvalues eta alpha p) := by
  have h1 := g73g_gad_diag eta alpha p heta halpha
  have hS : HasSpectrum (dampingJointOutput (gadChannel eta alpha) p (Real.pi/2) 0)
      (gadDiagonalEigenvalues eta alpha p) := by
    obtain ⟨e0, e1⟩ := heta; obtain ⟨a0, a1⟩ := halpha; obtain ⟨p0, p1⟩ := hp
    rw [g73g_joint_diag eta alpha p ⟨e0, e1⟩ ⟨a0, a1⟩ ⟨p0, p1⟩]
    unfold HasSpectrum
    rw [g73g_J_cp, Fin.prod_univ_four]
    set A := (1-alpha)*(1-p)+alpha*eta*(1-p) with hA
    set D := (1-alpha)*p*eta+alpha*p with hD
    set c := Real.sqrt eta * Real.sqrt (1-p) * Real.sqrt p with hc
    set u := alpha*(1-eta)*(1-p) with hu
    set v := (1-alpha)*(1-eta)*p with hv
    have hcc : c * c = eta*(1-p)*p := by
      rw [show c*c = (Real.sqrt eta * Real.sqrt eta) * (Real.sqrt (1-p) * Real.sqrt (1-p)) *
        (Real.sqrt p * Real.sqrt p) by ring, Real.mul_self_sqrt e0, Real.mul_self_sqrt (by linarith),
        Real.mul_self_sqrt p0]
    have hdisc : 1-2*(u+v)+(v-u)^2 = (A-D)^2 + 4*(c*c) := by rw [hcc, hA, hD, hu, hv]; ring
    have hdn : 0 ≤ 1-2*(u+v)+(v-u)^2 := by rw [hdisc]; nlinarith [sq_nonneg (A-D), mul_self_nonneg c]
    set t := Real.sqrt (1-2*(u+v)+(v-u)^2) with ht
    have htt : t * t = 1-2*(u+v)+(v-u)^2 := Real.mul_self_sqrt hdn
    have e3 : gadDiagonalEigenvalues eta alpha p 2 = (1-u-v+t)/2 := rfl
    have e4 : gadDiagonalEigenvalues eta alpha p 3 = (1-u-v-t)/2 := rfl
    have e1' : gadDiagonalEigenvalues eta alpha p 0 = u := rfl
    have e2' : gadDiagonalEigenvalues eta alpha p 1 = v := rfl
    rw [e1', e2', e3, e4]
    have hs : (A:ℂ) + D = (((1-u-v+t)/2 : ℝ) : ℂ) + (((1-u-v-t)/2 : ℝ) : ℂ) := by
      push_cast; rw [hA, hD, hu, hv]; push_cast; ring
    have hq : (A:ℂ) * D - c * c = (((1-u-v+t)/2 : ℝ) : ℂ) * (((1-u-v-t)/2 : ℝ) : ℂ) := by
      have : A * D - c * c = ((1-u-v+t)/2) * ((1-u-v-t)/2) := by
        have e : ((1-u-v+t)/2) * ((1-u-v-t)/2) = ((1-u-v)^2 - t*t)/4 := by ring
        rw [e, htt, hcc, hA, hD, hu, hv]; ring
      exact_mod_cast this
    rw [hs, hq]
    simp only [map_add, map_mul]
    ring
  refine ⟨h1, ?_, hS, ?_⟩
  · rw [h1, g73g_vn_diagInput]
  · rw [g73g_vn_spec _ _ _ hS, entropy4]
    obtain ⟨e0, e1⟩ := heta; obtain ⟨a0, a1⟩ := halpha; obtain ⟨p0, p1⟩ := hp
    rw [g73g_joint_diag eta alpha p ⟨e0, e1⟩ ⟨a0, a1⟩ ⟨p0, p1⟩]
    exact g73g_J_herm _ _ _ _ _

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

lemma g73g_gadBlock (eta alpha p theta : ℝ)
    (heta : eta ∈ Set.Icc (0 : ℝ) 1) (halpha : alpha ∈ Set.Icc (0 : ℝ) 1)
    (hp : p ∈ Set.Icc (0 : ℝ) 1) :
    dampingJointOutput (gadChannel eta alpha) p theta 0 = gadBlockMatrix eta alpha p theta := by
  obtain ⟨e0, e1⟩ := heta; obtain ⟨a0, a1⟩ := halpha; obtain ⟨p0, p1⟩ := hp
  have h1 := g73g_sq eta e0
  have h2 := g73g_sq (1-eta) (by linarith)
  push_cast at h2
  have h3 := g73g_sq alpha a0
  have h4 := g73g_sq (1-alpha) (by linarith)
  push_cast at h4
  have h5 := g73g_sq p p0
  have h6 := g73g_sq (1-p) (by linarith)
  push_cast at h6
  have hs : Real.sqrt (eta*(1-p)*p) = Real.sqrt eta * Real.sqrt (1-p) * Real.sqrt p := by
    rw [Real.sqrt_mul (by nlinarith), Real.sqrt_mul e0]
  ext ⟨x1, x2⟩ ⟨y1, y2⟩
  fin_cases x1 <;> fin_cases x2 <;> fin_cases y1 <;> fin_cases y2 <;>
  simp [dampingJointOutput, idTensorSuperop, gadChannel, krausApply, gadKraus, adKraus,
    pureDensity, inputPurification, Matrix.mul_apply, gadBlockMatrix, hs,
    Fin.sum_univ_four, Fin.sum_univ_two, Matrix.sum_apply, Matrix.conjTranspose_apply, -Complex.ofReal_cos, -Complex.ofReal_sin]
  all_goals (try ring_nf at h1 h2 h3 h4 h5 h6 ⊢)
  all_goals (try simp only [h1, h2, h3, h4, h5, h6])
  all_goals (try ring_nf)

lemma g73g_tl_gad (eta alpha p theta : ℝ)
    (heta : eta ∈ Set.Icc (0 : ℝ) 1) (halpha : alpha ∈ Set.Icc (0 : ℝ) 1)
    (hp : p ∈ Set.Icc (0 : ℝ) 1) :
    traceLeft (dampingJointOutput (gadChannel eta alpha) p theta 0) = g73g_R p theta := by
  rw [g73g_gadBlock eta alpha p theta heta halpha hp]
  ext i j; fin_cases i <;> fin_cases j <;>
  simp [traceLeft, gadBlockMatrix, g73g_R, Fin.sum_univ_two] <;> ring

lemma g73g_tl_ad (eta p theta : ℝ)
    (heta : eta ∈ Set.Icc (0 : ℝ) 1) (hp : p ∈ Set.Icc (0 : ℝ) 1) :
    traceLeft (dampingJointOutput (adChannel eta) p theta 0) = g73g_R p theta := by
  obtain ⟨e0, e1⟩ := heta; obtain ⟨p0, p1⟩ := hp
  have h1 := g73g_sq eta e0
  have h2 := g73g_sq (1-eta) (by linarith)
  push_cast at h2
  have h5 := g73g_sq p p0
  have h6 := g73g_sq (1-p) (by linarith)
  push_cast at h6
  ext i j; fin_cases i <;> fin_cases j <;>
  simp [traceLeft, dampingJointOutput, idTensorSuperop, adChannel, krausApply, adKraus,
    pureDensity, inputPurification, Matrix.mul_apply, g73g_R,
    Fin.sum_univ_two, Matrix.sum_apply, Matrix.conjTranspose_apply, -Complex.ofReal_cos, -Complex.ofReal_sin]
  all_goals (try ring_nf at h1 h2 h5 h6 ⊢)
  all_goals (try simp only [h1, h2, h5, h6])
  all_goals (try ring_nf)

theorem g73g_gadGen (eta alpha p theta : ℝ)
    (heta : eta ∈ Set.Icc (0 : ℝ) 1) (halpha : alpha ∈ Set.Icc (0 : ℝ) 1)
    (hp : p ∈ Set.Icc (0 : ℝ) 1) (htheta : theta ∈ Set.Icc (0 : ℝ) Real.pi) :
    dampingJointOutput (gadChannel eta alpha) p theta 0 = gadBlockMatrix eta alpha p theta ∧
    traceLeft (dampingJointOutput (gadChannel eta alpha) p theta 0) =
      traceLeft (dampingJointOutput (adChannel eta) p theta 0) ∧
    HasSpectrum (traceLeft (dampingJointOutput (gadChannel eta alpha) p theta 0))
      (adEigenvalues 1 p theta) ∧
    traceRight (dampingJointOutput (gadChannel eta alpha) p theta 0) =
      !![((1-(eta*p+(1-eta)*alpha) : ℝ) : ℂ), ((Real.sqrt (eta*(1-p)*p)*Real.cos theta : ℝ) : ℂ);
        ((Real.sqrt (eta*(1-p)*p)*Real.cos theta : ℝ) : ℂ), ((eta*p+(1-eta)*alpha : ℝ) : ℂ)] ∧
    HasSpectrum (traceRight (dampingJointOutput (gadChannel eta alpha) p theta 0))
      (gadBobEigenvalues eta alpha p theta) := by
  have hB := g73g_gadBlock eta alpha p theta heta halpha hp
  have hsc : (Real.sin theta : ℂ)^2 + (Real.cos theta : ℂ)^2 = 1 := by
    exact_mod_cast Real.sin_sq_add_cos_sq theta
  obtain ⟨e0, e1⟩ := heta; obtain ⟨a0, a1⟩ := halpha; obtain ⟨p0, p1⟩ := hp
  have hTR : traceRight (dampingJointOutput (gadChannel eta alpha) p theta 0) =
      !![((1-(eta*p+(1-eta)*alpha) : ℝ) : ℂ), ((Real.sqrt (eta*(1-p)*p)*Real.cos theta : ℝ) : ℂ);
        ((Real.sqrt (eta*(1-p)*p)*Real.cos theta : ℝ) : ℂ), ((eta*p+(1-eta)*alpha : ℝ) : ℂ)] := by
    rw [hB]
    ext i j; fin_cases i <;> fin_cases j <;>
    simp [traceRight, gadBlockMatrix, Fin.sum_univ_two, -Complex.ofReal_cos, -Complex.ofReal_sin]
    · linear_combination ((1-alpha)*p*(1-eta)) * hsc
    · linear_combination (p*(alpha+(1-alpha)*eta)) * hsc
  refine ⟨hB, ?_, ?_, hTR, ?_⟩
  · rw [g73g_tl_gad eta alpha p theta ⟨e0, e1⟩ ⟨a0, a1⟩ ⟨p0, p1⟩,
      g73g_tl_ad eta p theta ⟨e0, e1⟩ ⟨p0, p1⟩]
  · rw [g73g_tl_gad eta alpha p theta ⟨e0, e1⟩ ⟨a0, a1⟩ ⟨p0, p1⟩]
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
  · rw [hTR]
    have hdn : 0 ≤ (1-2*(p*eta+alpha*(1-eta)))^2 + 4*eta*p*(1-p)*(Real.cos theta)^2 := by
      have : 0 ≤ eta*p*(1-p) := mul_nonneg (mul_nonneg e0 p0) (by linarith)
      positivity
    have htt := Real.mul_self_sqrt hdn
    have hq : Real.sqrt (eta*(1-p)*p) ^ 2 = eta*(1-p)*p :=
      Real.sq_sqrt (mul_nonneg (mul_nonneg e0 (by linarith)) p0)
    simp only [gadBobEigenvalues]
    apply g73g_spec2
    · simp [Matrix.trace_fin_two]
    · rw [Matrix.det_fin_two]
      simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_cons]
      rw [htt]
      have : (1-(eta*p+(1-eta)*alpha)) * (eta*p+(1-eta)*alpha) -
          (Real.sqrt (eta*(1-p)*p)*Real.cos theta) * (Real.sqrt (eta*(1-p)*p)*Real.cos theta) =
          (1 - ((1-2*(p*eta+alpha*(1-eta)))^2 + 4*eta*p*(1-p)*(Real.cos theta)^2))/4 := by
        linear_combination (-(Real.cos theta)^2) * hq
      rw [← this]; push_cast; ring



/-- PDF p.6, Eqs.(25)–(28),(34),(35): actual GAD block output, unchanged Alice
reference marginal, and Bob's full spectrum. No use is made of printed Eq.(29). -/
theorem solution (eta alpha p theta : ℝ)
    (heta : eta ∈ Set.Icc (0 : ℝ) 1) (halpha : alpha ∈ Set.Icc (0 : ℝ) 1)
    (hp : p ∈ Set.Icc (0 : ℝ) 1) (htheta : theta ∈ Set.Icc (0 : ℝ) Real.pi) :
    dampingJointOutput (gadChannel eta alpha) p theta 0 = gadBlockMatrix eta alpha p theta ∧
    traceLeft (dampingJointOutput (gadChannel eta alpha) p theta 0) =
      traceLeft (dampingJointOutput (adChannel eta) p theta 0) ∧
    HasSpectrum (traceLeft (dampingJointOutput (gadChannel eta alpha) p theta 0))
      (adEigenvalues 1 p theta) ∧
    traceRight (dampingJointOutput (gadChannel eta alpha) p theta 0) =
      !![((1-(eta*p+(1-eta)*alpha) : ℝ) : ℂ), ((Real.sqrt (eta*(1-p)*p)*Real.cos theta : ℝ) : ℂ);
        ((Real.sqrt (eta*(1-p)*p)*Real.cos theta : ℝ) : ℂ), ((eta*p+(1-eta)*alpha : ℝ) : ℂ)] ∧
    HasSpectrum (traceRight (dampingJointOutput (gadChannel eta alpha) p theta 0))
      (gadBobEigenvalues eta alpha p theta) := by
  exact g73g_gadGen eta alpha p theta heta halpha hp htheta


end
