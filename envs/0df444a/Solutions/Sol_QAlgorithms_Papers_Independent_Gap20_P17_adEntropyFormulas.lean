-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Gap20.P17.adEntropyFormulas
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T21:15:59.74902+00:00
-- url     : https://prove2.me/submissions/f68ee1ea-d7c0-450f-8023-a9db20915acc

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



/-- PDF p.3, Eq.(9): survival eta, excited population p, including both endpoints.
The E argument printed in (9) denotes D_eta from the surrounding paragraph. -/
theorem solution (eta p : ℝ) (heta : eta ∈ Set.Icc (0 : ℝ) 1)
    (hp : p ∈ Set.Icc (0 : ℝ) 1) :
    adChannel eta (diagonalInput p) = diagonalInput (eta*p) ∧
    forwardInfo (adDilation eta) (diagonalInput p) =
      binEntropy2 (eta*p) - binEntropy2 ((1-eta)*p) ∧
    reverseInfo (adDilation eta) (diagonalInput p) =
      binEntropy2 p - binEntropy2 ((1-eta)*p) := by
  exact g73g_adEnt eta p heta hp


end
