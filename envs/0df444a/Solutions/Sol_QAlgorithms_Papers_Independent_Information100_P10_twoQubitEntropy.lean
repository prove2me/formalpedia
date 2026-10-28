-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Information100.P10.twoQubitEntropy
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T18:30:51.324214+00:00
-- url     : https://prove2.me/submissions/b8ce15d6-51fe-4385-8332-3840f7d2a818

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P10
import Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P10_geometricMinimum
namespace QAlgorithms.Papers.Independent.Information100.P10
open scoped ComplexConjugate Matrix ComplexOrder MatrixOrder

lemma e0 : natToBits 2 0 = ![false,false] := by decide
lemma e1 : natToBits 2 1 = ![false,true] := by decide
lemma e2 : natToBits 2 2 = ![true,false] := by decide
lemma e3 : natToBits 2 3 = ![true,true] := by decide

lemma E_inner_ket_act {ι : Type*} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℂ) (x y : ι) :
    inner ℂ (ket x : EuclideanSpace ℂ ι) (act A (ket y)) = A x y := by
  simp [ket, act, EuclideanSpace.inner_single_left, Matrix.mulVec_single]
lemma E_act_add {ι : Type*} [Fintype ι] (A : Matrix ι ι ℂ) (u v : EuclideanSpace ℂ ι) :
    act A (u + v) = act A u + act A v := by simp [act, Matrix.mulVec_add]
lemma E_act_smul {ι : Type*} [Fintype ι] (A : Matrix ι ι ℂ) (c : ℂ) (u : EuclideanSpace ℂ ι) :
    act A (c • u) = c • act A u := by simp [act, Matrix.mulVec_smul]
lemma E_norm_sq_act {ι : Type*} [Fintype ι] [DecidableEq ι] (v : EuclideanSpace ℂ ι) :
    ‖v‖ ^ 2 = (inner ℂ v (act 1 v)).re := by
  rw [@norm_sq_eq_re_inner ℂ]; simp [act]
lemma E_ket_apply {ι : Type*} [DecidableEq ι] (x y : ι) :
    (ket x : EuclideanSpace ℂ ι) y = if y = x then 1 else 0 := by
  simp [ket, EuclideanSpace.single_apply]

lemma E_q2 (P : Qubits 2 → Prop) (h : ∀ a b : Bool, P ![a, b]) : ∀ z, P z := by
  intro z
  have : z = ![z 0, z 1] := by funext i; fin_cases i <;> rfl
  rw [this]; exact h _ _

noncomputable def W2 (w0 w1 w2 w3 : ℂ) : Ket 2 :=
  w0 • ket ![false,false] + w1 • ket ![false,true] + w2 • ket ![true,false] + w3 • ket ![true,true]

lemma E_expand (psi : Ket 2) : psi =
    W2 (psi ![false,false]) (psi ![false,true]) (psi ![true,false]) (psi ![true,true]) := by
  unfold W2
  ext z; revert z
  refine E_q2 _ (fun a b => ?_)
  cases a <;> cases b <;> simp [E_ket_apply]

lemma W2_norm (w0 w1 w2 w3 : ℂ) : ‖W2 w0 w1 w2 w3‖ ^ 2 =
    (w0.re ^ 2 + w0.im ^ 2) + (w1.re ^ 2 + w1.im ^ 2) + (w2.re ^ 2 + w2.im ^ 2) + (w3.re ^ 2 + w3.im ^ 2) := by
  rw [E_norm_sq_act]
  simp only [W2, E_act_add, E_act_smul, inner_add_left, inner_add_right, inner_smul_left, inner_smul_right,
    E_inner_ket_act]
  simp [Matrix.one_apply]
  ring

lemma W2_bloch (w0 w1 w2 w3 : ℂ) : ‖bloch (W2 w0 w1 w2 w3) 0‖ ^ 2 + ‖bloch (W2 w0 w1 w2 w3) 1‖ ^ 2 =
    (2 * (w0.re * w2.re + w0.im * w2.im + w1.re * w3.re + w1.im * w3.im)) ^ 2 +
    (2 * (w0.re * w2.im - w0.im * w2.re + w1.re * w3.im - w1.im * w3.re)) ^ 2 +
    ((w0.re ^ 2 + w0.im ^ 2) + (w1.re ^ 2 + w1.im ^ 2) - (w2.re ^ 2 + w2.im ^ 2) - (w3.re ^ 2 + w3.im ^ 2)) ^ 2 +
    ((2 * (w0.re * w1.re + w0.im * w1.im + w2.re * w3.re + w2.im * w3.im)) ^ 2 +
    (2 * (w0.re * w1.im - w0.im * w1.re + w2.re * w3.im - w2.im * w3.re)) ^ 2 +
    ((w0.re ^ 2 + w0.im ^ 2) - (w1.re ^ 2 + w1.im ^ 2) + (w2.re ^ 2 + w2.im ^ 2) - (w3.re ^ 2 + w3.im ^ 2)) ^ 2) := by
  simp only [EuclideanSpace.norm_sq_eq, Fin.sum_univ_three, Real.norm_eq_abs, sq_abs]
  simp only [bloch, PiLp.toLp_apply, W2, E_act_add, E_act_smul, inner_add_left, inner_add_right, inner_smul_left,
    inner_smul_right, E_inner_ket_act, localPauli, kronAll, Matrix.of_apply, Fin.prod_univ_two]
  simp [pauli, pauliX, pauliY, pauliZ, Matrix.one_apply]
  ring

lemma W2_conj (w0 w1 w2 w3 : ℂ) : (WithLp.toLp 2 (fun z => conj (W2 w0 w1 w2 w3 z)) : Ket 2) =
    W2 (conj w0) (conj w1) (conj w2) (conj w3) := by
  ext z; revert z
  refine E_q2 _ (fun a b => ?_)
  cases a <;> cases b <;> simp [W2, E_ket_apply]

lemma W2_conc (w0 w1 w2 w3 : ℂ) : concurrence (W2 w0 w1 w2 w3) ^ 2 =
    4 * ((w0.re * w3.re - w0.im * w3.im - (w1.re * w2.re - w1.im * w2.im)) ^ 2 +
      (w0.re * w3.im + w0.im * w3.re - (w1.re * w2.im + w1.im * w2.re)) ^ 2) := by
  unfold concurrence
  rw [W2_conj, Complex.sq_norm, Complex.normSq_apply]
  simp only [W2, E_act_add, E_act_smul, inner_add_left, inner_add_right, inner_smul_left,
    inner_smul_right, E_inner_ket_act, kronAll, Matrix.of_apply, Fin.prod_univ_two]
  simp [pauliY]
  ring


lemma W2_ED (w0 w1 w2 w3 : ℂ) (hpsi : IsState (W2 w0 w1 w2 w3)) :
    entanglementDistance (W2 w0 w1 w2 w3) =
      8 * ((w0.re * w3.re - w0.im * w3.im - (w1.re * w2.re - w1.im * w2.im)) ^ 2 +
        (w0.re * w3.im + w0.im * w3.re - (w1.re * w2.im + w1.im * w2.re)) ^ 2) := by
  have hED := (geometricMinimum _ hpsi).2.2.2.2.1
  simp only [Fin.sum_univ_two, Nat.cast_ofNat] at hED
  have hn := W2_norm w0 w1 w2 w3
  rw [show ‖W2 w0 w1 w2 w3‖ = 1 from hpsi, one_pow] at hn
  rw [hED, W2_bloch]
  linear_combination (2 * ((w0.re ^ 2 + w0.im ^ 2) + (w1.re ^ 2 + w1.im ^ 2) + (w2.re ^ 2 + w2.im ^ 2) + (w3.re ^ 2 + w3.im ^ 2) + 1)) * hn

lemma red_eq (psi : Ket 2) : reducedFirst psi =
    (Matrix.of fun j h => psi ![j, h]) * (Matrix.of fun j h => psi ![j, h])ᴴ := by
  ext j k
  simp [reducedFirst, traceRight, pureDensity, Matrix.mul_apply]

lemma red_entries (w0 w1 w2 w3 : ℂ) :
    reducedFirst (W2 w0 w1 w2 w3) false false = w0 * conj w0 + w1 * conj w1 ∧
    reducedFirst (W2 w0 w1 w2 w3) true true = w2 * conj w2 + w3 * conj w3 ∧
    reducedFirst (W2 w0 w1 w2 w3) false true = w0 * conj w2 + w1 * conj w3 ∧
    reducedFirst (W2 w0 w1 w2 w3) true false = w2 * conj w0 + w3 * conj w1 := by
  simp [reducedFirst, traceRight, pureDensity, W2, E_ket_apply]
  refine ⟨by ring, by ring, by ring, by ring⟩

lemma det_bool (A : Matrix Bool Bool ℂ) : A.det = A false false * A true true - A false true * A true false := by
  rw [← Matrix.det_submatrix_equiv_self finTwoEquiv.symm.symm A]
  rw [Matrix.det_fin_two]
  simp [finTwoEquiv]

lemma S172F_cfc_trace {n : Type*} [Fintype n] [DecidableEq n] {Y : Matrix n n ℂ} (hY : Y.IsHermitian)
    (f : ℝ → ℝ) : (cfc f Y).trace = ∑ i, ((f (hY.eigenvalues i) : ℝ) : ℂ) := by
  rw [hY.cfc_eq f, Matrix.IsHermitian.cfc, Unitary.conjStarAlgAut_apply, Matrix.trace_mul_cycle,
    Unitary.star_mul_self_of_mem hY.eigenvectorUnitary.2, one_mul, Matrix.trace_diagonal]
  rfl

lemma profile_mono (kB : ℝ) (hkB : 0 < kB) : StrictMonoOn (entropyProfile kB) (Set.Icc 0 2) := by
  intro x hx y hy hxy
  simp only [Set.mem_Icc] at hx hy
  unfold entropyProfile
  refine mul_lt_mul_of_pos_left ?_ hkB
  have g1 : ∀ e, 0 ≤ e → e ≤ 2 → (1 + Real.sqrt (1 - e / 2)) / 2 ∈ Set.Icc (2⁻¹ : ℝ) 1 := by
    intro e h0 h2
    have := Real.sqrt_nonneg (1 - e / 2)
    have : Real.sqrt (1 - e / 2) ≤ 1 := Real.sqrt_le_one.2 (by linarith)
    constructor <;> linarith
  refine Real.binEntropy_strictAntiOn (g1 y hy.1 hy.2) (g1 x hx.1 hx.2) ?_
  have : Real.sqrt (1 - y / 2) < Real.sqrt (1 - x / 2) := Real.sqrt_lt_sqrt (by linarith) (by linarith)
  linarith

lemma binEnt_eq (a b : ℝ) (hab : a + b = 1) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    Real.binEntropy ((1 + Real.sqrt (1 - 8 * (a * b) / 2)) / 2) = -(a * Real.log a + b * Real.log b) := by
  have hsq : 1 - 8 * (a * b) / 2 = (a - b) ^ 2 := by
    have : b = 1 - a := by linarith
    subst this; ring
  rw [hsq, Real.sqrt_sq_eq_abs]
  unfold Real.binEntropy
  rw [Real.log_inv, Real.log_inv]
  rcases le_total b a with h | h
  · rw [abs_of_nonneg (by linarith)]
    rw [show (1 + (a - b)) / 2 = a by linarith, show 1 - a = b by linarith]
    ring
  · rw [abs_of_nonpos (by linarith)]
    rw [show (1 + -(a - b)) / 2 = b by linarith, show 1 - b = a by linarith]
    ring

end QAlgorithms.Papers.Independent.Information100.P10

open QAlgorithms QAlgorithms.Papers QAlgorithms.Papers.Independent QAlgorithms.Papers.Independent.Information100 QAlgorithms.Papers.Independent.Information100.P10 in
open scoped ComplexConjugate Matrix ComplexOrder in
theorem solution (psi : Ket 2) (hpsi : IsState psi)
    (kB : ℝ) (hkB : 0 < kB) :
    IsDensityMatrix (reducedFirst psi) ∧
    entanglementDistance psi ∈ Set.Icc (0 : ℝ) 2 ∧
    entropyOfEntanglement kB psi = entropyProfile kB (entanglementDistance psi) ∧
    StrictMonoOn (entropyProfile kB) (Set.Icc 0 2) := by
  have hE := E_expand psi
  set w0 := psi ![false, false]
  set w1 := psi ![false, true]
  set w2 := psi ![true, false]
  set w3 := psi ![true, true]
  clear_value w0 w1 w2 w3
  subst hE
  have hn := W2_norm w0 w1 w2 w3
  rw [show ‖W2 w0 w1 w2 w3‖ = 1 from hpsi, one_pow] at hn
  have hED := W2_ED w0 w1 w2 w3 hpsi
  obtain ⟨r00, r11, r01, r10⟩ := red_entries w0 w1 w2 w3
  have hρ : IsDensityMatrix (reducedFirst (W2 w0 w1 w2 w3)) := by
    refine ⟨?_, ?_⟩
    · rw [red_eq]; exact Matrix.posSemidef_self_mul_conjTranspose _
    · rw [Matrix.trace, Fintype.sum_bool]
      simp only [Matrix.diag, r00, r11]
      apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im] <;> linarith
  set K := (w0.re * w3.re - w0.im * w3.im - (w1.re * w2.re - w1.im * w2.im)) ^ 2 +
        (w0.re * w3.im + w0.im * w3.re - (w1.re * w2.im + w1.im * w2.re)) ^ 2 with hK
  have hdet : (reducedFirst (W2 w0 w1 w2 w3)).det = (K : ℂ) := by
    rw [det_bool, r00, r11, r01, r10]
    apply Complex.ext
    · simp only [Complex.sub_re, Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im, Complex.conj_re,
        Complex.conj_im, Complex.ofReal_re]
      rw [hK]; ring
    · simp only [Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im, Complex.conj_re,
        Complex.conj_im, Complex.ofReal_im]
      ring
  have hH := hρ.1.1
  set a := hH.eigenvalues true
  set b := hH.eigenvalues false
  have ha : 0 ≤ a := hρ.1.eigenvalues_nonneg true
  have hb : 0 ≤ b := hρ.1.eigenvalues_nonneg false
  have hab : a + b = 1 := by
    have h1 := hH.trace_eq_sum_eigenvalues
    rw [hρ.2, Fintype.sum_bool] at h1
    have := congrArg Complex.re h1
    simp at this
    linarith
  have hprod : a * b = K := by
    have h1 := hH.det_eq_prod_eigenvalues
    rw [hdet, Fintype.prod_bool] at h1
    have := congrArg Complex.re h1
    simp at this
    linarith
  refine ⟨hρ, ?_, ?_, profile_mono kB hkB⟩
  · rw [hED, ← hprod]
    constructor
    · nlinarith
    · nlinarith [sq_nonneg (a - b)]
  · rw [hED, ← hprod]
    unfold entropyOfEntanglement entropyProfile vnEntropy
    rw [binEnt_eq a b hab ha hb]
    rw [S172F_cfc_trace hH, Fintype.sum_bool]
    simp only [Complex.add_re, Complex.ofReal_re]
    have hl : Real.log 2 ≠ 0 := by positivity
    simp only [Real.logb]
    field_simp
    ring
