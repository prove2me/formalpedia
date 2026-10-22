-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Gap20.P17.reverseInformation_noDataProcessing
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T21:25:15.299533+00:00
-- url     : https://prove2.me/submissions/c0a4d892-8cc4-4b18-b073-dd11032a0ba3

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

lemma g73g_trace_cfc_eq {X Y : Type*} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
    (P : Matrix X X ℂ) (Q : Matrix Y Y ℂ) (hP : P.IsHermitian) (hQ : Q.IsHermitian)
    (f : ℝ → ℝ) (hf : f 0 = 0) (htr : ∀ k : ℕ, (P ^ (k + 1)).trace = (Q ^ (k + 1)).trace) :
    (cfc f P).trace = (cfc f Q).trace := by
  classical
  set S : Finset ℝ := (P.finite_real_spectrum.union Q.finite_real_spectrum).toFinset ∪ {0} with hS
  set p : Polynomial ℝ := Lagrange.interpolate S id f with hp
  have hev : ∀ x ∈ S, p.eval x = f x := by
    intro x hx
    have := Lagrange.eval_interpolate_at_node (s := S) (v := id) f (Set.injOn_id _) hx
    exact this
  have hPe : cfc f P = Polynomial.aeval P p := by
    rw [← cfc_polynomial p P hP.isSelfAdjoint]
    apply cfc_congr
    intro x hx
    exact (hev x (by simp [hS, hx])).symm
  have hQe : cfc f Q = Polynomial.aeval Q p := by
    rw [← cfc_polynomial p Q hQ.isSelfAdjoint]
    apply cfc_congr
    intro x hx
    exact (hev x (by simp [hS, hx])).symm
  have h0 : p.coeff 0 = 0 := by
    rw [Polynomial.coeff_zero_eq_eval_zero, hev 0 (by simp [hS]), hf]
  rw [hPe, hQe, Polynomial.aeval_eq_sum_range, Polynomial.aeval_eq_sum_range,
    Matrix.trace_sum, Matrix.trace_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Matrix.trace_smul, Matrix.trace_smul]
  rcases i with _ | k
  · simp [h0]
  · rw [htr k]

lemma g73g_pow_succ_mul {X Y : Type*} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
    (M : Matrix X Y ℂ) (k : ℕ) : (M * Mᴴ) ^ (k + 1) = M * (Mᴴ * M) ^ k * Mᴴ := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, ih, pow_succ]
    simp only [Matrix.mul_assoc]


def g73g_s : ℝ := Real.sqrt (1/2)

lemma g73g_ssC : (g73g_s : ℂ) * (g73g_s : ℂ) = 1/2 := by
  rw [g73g_s, g73g_sqC _ (by norm_num)]; push_cast; ring

def g73g_V : Matrix (Fin 2 × Fin 4) (Fin 2) ℂ := fun be a =>
  if a = 0 then (if be.1.val = be.2.val then (g73g_s : ℂ) else 0)
  else (if be.1 = 0 ∧ be.2 = 2 then 1 else 0)

def g73g_W : Matrix (Fin 2 × Fin 2) (Fin 2) ℂ := fun cf b => if cf.1 = 0 ∧ cf.2 = b then 1 else 0

def g73g_A : Matrix (Fin 4 × Fin 2) (Fin 1) ℂ := fun ef _ =>
  if ef.1.val = ef.2.val then (g73g_s : ℂ) else 0

lemma g73g_V_iso : IsIsometry g73g_V := by
  unfold IsIsometry
  ext i j; fin_cases i <;> fin_cases j <;>
  simp [g73g_V, Matrix.mul_apply, Fin.sum_univ_two, Fin.sum_univ_four, Fintype.sum_prod_type,
    Matrix.conjTranspose_apply, g73g_ssC]
  norm_num

lemma g73g_W_iso : IsIsometry g73g_W := by
  unfold IsIsometry
  ext i j; fin_cases i <;> fin_cases j <;>
  simp [g73g_W, Matrix.mul_apply, Fin.sum_univ_two, Fintype.sum_prod_type,
    Matrix.conjTranspose_apply]

open scoped ComplexOrder in
lemma g73g_rho_dens : IsDensityMatrix (diagonalInput 0) := by
  refine ⟨?_, ?_⟩
  · rw [g73g_diag_eq]
    apply Matrix.PosSemidef.diagonal
    intro i; fin_cases i <;> simp
  · simp [diagonalInput, Matrix.trace_fin_two]

lemma g73g_envV : complementaryChannel g73g_V (diagonalInput 0) =
    Matrix.diagonal (fun i => ((![1/2, 1/2, 0, 0] : Fin 4 → ℝ) i : ℂ)) := by
  ext i j; fin_cases i <;> fin_cases j <;>
  simp [complementaryChannel, traceLeft, g73g_V, diagonalInput, Matrix.mul_apply, Fin.sum_univ_two,
    Fin.sum_univ_four, Fintype.sum_prod_type, Matrix.conjTranspose_apply, g73g_ssC]

lemma g73g_envVW : complementaryChannel (composeDilation g73g_V g73g_W) (diagonalInput 0) =
    g73g_A * g73g_Aᴴ := by
  ext ⟨e, f⟩ ⟨e', f'⟩; fin_cases e <;> fin_cases f <;> fin_cases e' <;> fin_cases f' <;>
  simp [complementaryChannel, traceLeft, composeDilation, g73g_V, g73g_W, g73g_A, diagonalInput,
    Matrix.mul_apply, Fin.sum_univ_two, Fin.sum_univ_four, Fintype.sum_prod_type,
    Matrix.conjTranspose_apply, g73g_ssC]

lemma g73g_AA : g73g_Aᴴ * g73g_A = 1 := by
  ext i j; fin_cases i; fin_cases j
  simp [g73g_A, Matrix.mul_apply, Fin.sum_univ_two, Fin.sum_univ_four, Fintype.sum_prod_type,
    Matrix.conjTranspose_apply, g73g_ssC]
  norm_num

lemma g73g_pow (k : ℕ) : ((g73g_A * g73g_Aᴴ) ^ (k+1)).trace =
    ((1 : Matrix (Fin 1) (Fin 1) ℂ) ^ (k+1)).trace := by
  have : (g73g_A * g73g_Aᴴ) ^ (k+1) = g73g_A * g73g_Aᴴ := by
    induction k with
    | zero => simp
    | succ k ih => rw [pow_succ, ih, Matrix.mul_assoc, ← Matrix.mul_assoc g73g_Aᴴ, g73g_AA,
        Matrix.one_mul]
  rw [this, one_pow, Matrix.trace_mul_comm, g73g_AA]

lemma g73g_vnA : vnEntropy (g73g_A * g73g_Aᴴ) = 0 := by
  have h := g73g_trace_cfc_eq (g73g_A * g73g_Aᴴ) (1 : Matrix (Fin 1) (Fin 1) ℂ)
    (Matrix.isHermitian_mul_conjTranspose_self _) Matrix.isHermitian_one
    (fun x : ℝ => x * Real.logb 2 x) (by simp) g73g_pow
  unfold vnEntropy; rw [h]
  have h1 : (1 : Matrix (Fin 1) (Fin 1) ℂ) = Matrix.diagonal (fun i => (((fun _ => 1) : Fin 1 → ℝ) i : ℂ)) := by
    simp
  rw [h1, g73g_trace_cfc_diag]; simp

theorem g73g_noDP :
    ∃ V : Matrix (Fin 2 × Fin 4) (Fin 2) ℂ,
    ∃ W : Matrix (Fin 2 × Fin 2) (Fin 2) ℂ,
    ∃ rho : Matrix (Fin 2) (Fin 2) ℂ,
      IsIsometry V ∧ IsIsometry W ∧ IsDensityMatrix rho ∧
      reverseInfo V rho < reverseInfo (composeDilation V W) rho := by
  refine ⟨g73g_V, g73g_W, diagonalInput 0, g73g_V_iso, g73g_W_iso, g73g_rho_dens, ?_⟩
  unfold reverseInfo
  rw [g73g_envV, g73g_envVW, g73g_vnA, g73g_vn_diag]
  simp [Fin.sum_univ_four, Real.logb]
  rw [neg_div, div_self (Real.log_pos one_lt_two).ne']; norm_num



/-- PDF p.3: failure of a universal output data-processing inequality, stated as
existence of two physical channels and a normalized input witnessing an increase. -/
theorem solution :
    ∃ V : Matrix (Fin 2 × Fin 4) (Fin 2) ℂ,
    ∃ W : Matrix (Fin 2 × Fin 2) (Fin 2) ℂ,
    ∃ rho : Matrix (Fin 2) (Fin 2) ℂ,
      IsIsometry V ∧ IsIsometry W ∧ IsDensityMatrix rho ∧
      reverseInfo V rho < reverseInfo (composeDilation V W) rho := by
  exact g73g_noDP


end
