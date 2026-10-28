-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Gap48.P40.relativeEntropyGradient
-- status  : ACCEPTED   (prove)
-- author  : @Alien60
-- created : 2026-10-26T22:13:05.623996+00:00
-- url     : https://prove2.me/submissions/6d17bcf6-15ac-43c6-8155-1c402efabfb1

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P40

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder Topology Matrix.Norms.L2Operator

open Filter MeasureTheory Asymptotics

open QAlgorithms

open QAlgorithms.Papers.Independent.Dependency50.P21 (relativeEntropy)

open QAlgorithms.Papers.Independent.Information100.P50 (IsUINorm)

open QAlgorithms.Papers.Independent.Information100.P56 (entropy)

open QAlgorithms.Papers.Independent.Information100.P60 (copies)

open QAlgorithms.Papers.Independent.Information100.P44 (Mat)

namespace QAlgorithms.Papers.Independent.Gap48.P40

section RegHelpers

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Double-sum formula for the trace of a product of two unitarily diagonalized matrices. -/
theorem reg_trace_conj_mul (U V : Matrix.unitaryGroup n ℂ) (F G : n → ℝ) :
    ((V : Matrix n n ℂ) * Matrix.diagonal (fun i => (F i : ℂ)) * star (V : Matrix n n ℂ) *
      ((U : Matrix n n ℂ) * Matrix.diagonal (fun j => (G j : ℂ)) * star (U : Matrix n n ℂ))).trace
      = ∑ i, ∑ j, ((F i * G j * Complex.normSq ((star (V : Matrix n n ℂ) * U) i j) : ℝ) : ℂ) := by
  set W : Matrix n n ℂ := star (V : Matrix n n ℂ) * U with hW
  have hstar : star W = star (U : Matrix n n ℂ) * V := by
    simp [hW, StarMul.star_mul]
  have key : ((V : Matrix n n ℂ) * Matrix.diagonal (fun i => (F i : ℂ)) * star (V : Matrix n n ℂ) *
      ((U : Matrix n n ℂ) * Matrix.diagonal (fun j => (G j : ℂ)) * star (U : Matrix n n ℂ))).trace
      = (Matrix.diagonal (fun i => (F i : ℂ)) * W * Matrix.diagonal (fun j => (G j : ℂ)) *
          star W).trace := by
    rw [hstar, hW]
    simp only [Matrix.mul_assoc]
    rw [Matrix.trace_mul_comm]
    simp only [Matrix.mul_assoc]
  rw [key, Matrix.trace]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Matrix.diag_apply, Matrix.mul_apply, Matrix.diagonal_apply, Matrix.star_apply,
    ite_mul, zero_mul, mul_ite, mul_zero, Finset.sum_ite_eq, Finset.sum_ite_eq',
    Finset.mem_univ, if_true]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Complex.ofReal_mul, Complex.ofReal_mul, Complex.normSq_eq_conj_mul_self, Complex.star_def]
  ring

/-- Rows of the overlap probabilities of two unitaries sum to one. -/
theorem reg_row_sum (U V : Matrix.unitaryGroup n ℂ) (i : n) :
    ∑ j, Complex.normSq ((star (V : Matrix n n ℂ) * U) i j) = 1 := by
  set W : Matrix n n ℂ := star (V : Matrix n n ℂ) * U with hW
  have hWu : W ∈ Matrix.unitaryGroup n ℂ := by
    rw [hW]
    exact (star V * U).2
  have h1 : (W * star W) i i = 1 := by
    rw [Matrix.mem_unitaryGroup_iff.mp hWu]; simp
  have h2 : (W * star W) i i = ((∑ j, Complex.normSq (W i j) : ℝ) : ℂ) := by
    simp only [Matrix.mul_apply, Matrix.star_apply, Complex.ofReal_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← Complex.mul_conj]; rfl
  exact_mod_cast h2.symm.trans h1

/-- Scalar estimate for `h(b,a) = b log b - b log a - b + a`. -/
theorem reg_scalar {a b c : ℝ} (hc : 0 < c) (ha : c ≤ a) (hb : 0 ≤ b) :
    0 ≤ b * Real.log b - b * Real.log a - b + a ∧
      b * Real.log b - b * Real.log a - b + a ≤ (b - a) ^ 2 / c := by
  have ha0 : 0 < a := lt_of_lt_of_le hc ha
  rcases hb.lt_or_eq with hb | hb
  · constructor
    · have := Real.log_le_sub_one_of_pos (div_pos ha0 hb)
      rw [Real.log_div ha0.ne' hb.ne'] at this
      have h2 := mul_le_mul_of_nonneg_left this hb.le
      have h3 : b * (a / b - 1) = a - b := by field_simp
      nlinarith
    · have := Real.log_le_sub_one_of_pos (div_pos hb ha0)
      rw [Real.log_div hb.ne' ha0.ne'] at this
      have h2 := mul_le_mul_of_nonneg_left this hb.le
      have h3 : b * (b / a - 1) - b + a = (b - a) ^ 2 / a := by field_simp; ring
      have h4 : (b - a) ^ 2 / a ≤ (b - a) ^ 2 / c :=
        div_le_div_of_nonneg_left (sq_nonneg _) hc ha
      nlinarith
  · subst hb
    simp only [Real.log_zero, mul_zero, zero_mul, sub_zero, zero_sub, zero_add]
    refine ⟨ha0.le, ?_⟩
    rw [neg_sq, le_div_iff₀ hc]
    nlinarith

/-- Overlap probabilities between the eigenbases of two Hermitian matrices. -/
noncomputable def reg_P {A B : Matrix n n ℂ} (hA : A.IsHermitian) (hB : B.IsHermitian) (i j : n) : ℝ :=
  Complex.normSq ((star (hB.eigenvectorUnitary : Matrix n n ℂ) * hA.eigenvectorUnitary) i j)

theorem reg_P_nonneg {A B : Matrix n n ℂ} (hA : A.IsHermitian) (hB : B.IsHermitian) (i j : n) :
    0 ≤ reg_P hA hB i j := Complex.normSq_nonneg _

theorem reg_P_row {A B : Matrix n n ℂ} (hA : A.IsHermitian) (hB : B.IsHermitian) (i : n) :
    ∑ j, reg_P hA hB i j = 1 := reg_row_sum _ _ i

theorem reg_trace_cfc {A B : Matrix n n ℂ} (hA : A.IsHermitian) (hB : B.IsHermitian)
    (f g : ℝ → ℝ) :
    (cfc f B * cfc g A).trace = ((∑ i, ∑ j, f (hB.eigenvalues i) * g (hA.eigenvalues j) *
      reg_P hA hB i j : ℝ) : ℂ) := by
  rw [hB.cfc_eq, hA.cfc_eq]
  simp only [Matrix.IsHermitian.cfc, Unitary.conjStarAlgAut_apply]
  have := reg_trace_conj_mul hA.eigenvectorUnitary hB.eigenvectorUnitary
    (f ∘ hB.eigenvalues) (g ∘ hA.eigenvalues)
  push_cast at this ⊢
  convert this using 1 <;> rfl

theorem reg_main_bound {A D : Matrix n n ℂ} (hA : A.IsHermitian) (hD : D.IsHermitian)
    {c : ℝ} (hc : 0 < c) (hev : ∀ j, c ≤ hA.eigenvalues j)
    (hQ : (D * D).trace.re < c ^ 2) :
    |(cfc (fun x : ℝ => x * Real.log x) (A + D) - (A + D) * cfc Real.log A - (A + D) + A).trace.re|
      ≤ (D * D).trace.re / c := by
  have hB : (A + D).IsHermitian := hA.add hD
  set a := hA.eigenvalues
  set b := hB.eigenvalues
  set P := reg_P hA hB
  have hsa : IsSelfAdjoint A := hA
  have hsb : IsSelfAdjoint (A + D) := hB
  have one_A : (1 : Matrix n n ℂ) = cfc (fun _ : ℝ => (1 : ℝ)) A := (cfc_const_one ℝ A).symm
  have one_B : (1 : Matrix n n ℂ) = cfc (fun _ : ℝ => (1 : ℝ)) (A + D) :=
    (cfc_const_one ℝ (A + D)).symm
  have id_A : A = cfc (fun x : ℝ => x) A := (cfc_id' ℝ A).symm
  have id_B : A + D = cfc (fun x : ℝ => x) (A + D) := (cfc_id' ℝ (A + D)).symm
  have sq_A : A * A = cfc (fun x : ℝ => x * x) A := by
    rw [cfc_mul (fun x : ℝ => x) (fun x : ℝ => x) A, cfc_id' ℝ A]
  have sq_B : (A + D) * (A + D) = cfc (fun x : ℝ => x * x) (A + D) := by
    rw [cfc_mul (fun x : ℝ => x) (fun x : ℝ => x) (A + D), cfc_id' ℝ (A + D)]
  -- the remainder as a double sum
  have hR : (cfc (fun x : ℝ => x * Real.log x) (A + D) - (A + D) * cfc Real.log A - (A + D) + A).trace.re
      = ∑ i, ∑ j, P i j * (b i * Real.log (b i) - b i * Real.log (a j) - b i + a j) := by
    have e1 : (cfc (fun x : ℝ => x * Real.log x) (A + D)).trace
        = (cfc (fun x : ℝ => x * Real.log x) (A + D) * cfc (fun _ : ℝ => (1 : ℝ)) A).trace := by
      rw [← one_A, Matrix.mul_one]
    have e2 : ((A + D) * cfc Real.log A).trace
        = (cfc (fun x : ℝ => x) (A + D) * cfc Real.log A).trace := by rw [← id_B]
    have e3 : (A + D).trace = (cfc (fun x : ℝ => x) (A + D) * cfc (fun _ : ℝ => (1 : ℝ)) A).trace := by
      rw [← id_B, ← one_A, Matrix.mul_one]
    have e4 : A.trace = (cfc (fun _ : ℝ => (1 : ℝ)) (A + D) * cfc (fun x : ℝ => x) A).trace := by
      rw [← id_A, ← one_B, Matrix.one_mul]
    rw [Matrix.trace_add, Matrix.trace_sub, Matrix.trace_sub, e1, e2, e3, e4]
    simp only [reg_trace_cfc hA hB]
    simp only [Complex.add_re, Complex.sub_re, Complex.ofReal_re]
    simp only [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  have hQe : (D * D).trace.re = ∑ i, ∑ j, P i j * (b i - a j) ^ 2 := by
    have hDD : D * D = (A + D) * (A + D) - (A + D) * A - A * (A + D) + A * A := by
      noncomm_ring
    have e1 : ((A + D) * (A + D)).trace
        = (cfc (fun x : ℝ => x * x) (A + D) * cfc (fun _ : ℝ => (1 : ℝ)) A).trace := by
      rw [← one_A, Matrix.mul_one, sq_B]
    have e2 : ((A + D) * A).trace = (cfc (fun x : ℝ => x) (A + D) * cfc (fun x : ℝ => x) A).trace := by
      rw [← id_A, ← id_B]
    have e3 : (A * (A + D)).trace = (cfc (fun x : ℝ => x) (A + D) * cfc (fun x : ℝ => x) A).trace := by
      rw [Matrix.trace_mul_comm, e2]
    have e4 : (A * A).trace = (cfc (fun _ : ℝ => (1 : ℝ)) (A + D) * cfc (fun x : ℝ => x * x) A).trace := by
      rw [← one_B, Matrix.one_mul, sq_A]
    rw [hDD, Matrix.trace_add, Matrix.trace_sub, Matrix.trace_sub, e1, e2, e3, e4]
    simp only [reg_trace_cfc hA hB]
    simp only [Complex.add_re, Complex.sub_re, Complex.ofReal_re]
    simp only [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  -- all eigenvalues of A + D are nonnegative
  have hb : ∀ i, 0 ≤ b i := by
    intro i
    by_contra hneg
    rw [not_le] at hneg
    have hrow : c ^ 2 ≤ ∑ j, P i j * (b i - a j) ^ 2 := by
      calc c ^ 2 = ∑ j, P i j * c ^ 2 := by
            rw [← Finset.sum_mul, reg_P_row hA hB i, one_mul]
        _ ≤ ∑ j, P i j * (b i - a j) ^ 2 := by
            refine Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left ?_ (reg_P_nonneg hA hB i j)
            have := hev j
            nlinarith
    have hall : ∑ j, P i j * (b i - a j) ^ 2 ≤ ∑ i, ∑ j, P i j * (b i - a j) ^ 2 :=
      Finset.single_le_sum (f := fun i => ∑ j, P i j * (b i - a j) ^ 2)
        (fun i _ => Finset.sum_nonneg fun j _ =>
          mul_nonneg (reg_P_nonneg hA hB i j) (sq_nonneg _)) (Finset.mem_univ i)
    linarith
  rw [hR, hQe, abs_le]
  have hlo : 0 ≤ ∑ i, ∑ j, P i j * (b i * Real.log (b i) - b i * Real.log (a j) - b i + a j) :=
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ =>
      mul_nonneg (reg_P_nonneg hA hB i j) (reg_scalar hc (hev j) (hb i)).1
  have hup : ∑ i, ∑ j, P i j * (b i * Real.log (b i) - b i * Real.log (a j) - b i + a j)
      ≤ (∑ i, ∑ j, P i j * (b i - a j) ^ 2) / c := by
    rw [Finset.sum_div]
    refine Finset.sum_le_sum fun i _ => ?_
    rw [Finset.sum_div]
    refine Finset.sum_le_sum fun j _ => ?_
    rw [mul_div_assoc]
    exact mul_le_mul_of_nonneg_left (reg_scalar hc (hev j) (hb i)).2 (reg_P_nonneg hA hB i j)
  have hQnn : 0 ≤ (∑ i, ∑ j, P i j * (b i - a j) ^ 2) / c :=
    div_nonneg (Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ =>
      mul_nonneg (reg_P_nonneg hA hB i j) (sq_nonneg _)) hc.le
  constructor <;> linarith

end RegHelpers

/-- PDF p.2, Lemma 1. -/
theorem reg_main {d : ℕ} (hd : 0 < d) (rho sigma : Mat d)
    (hrho : rho.PosDef) (hsigma : sigma.PosDef) :
    (fun D : Mat d => (relativeEntropy (rho + D) sigma).toReal -
      (relativeEntropy rho sigma).toReal -
      (D * (1 + cfc Real.log rho - cfc Real.log sigma)).trace.re)
      =o[nhdsWithin 0 {D : Mat d | D.IsHermitian}] (fun D : Mat d => D) := by
  have hA : rho.IsHermitian := hrho.isHermitian
  -- the support condition always holds since sigma is invertible
  have hsupp : ∀ X : Mat d,
      QAlgorithms.Papers.Independent.Dependency50.P21.IsSupported X sigma := by
    intro X v hv
    have hu : IsUnit sigma.det := isUnit_iff_ne_zero.mpr hsigma.det_pos.ne'
    have hv' : sigma *ᵥ v = 0 := hv
    have : v = 0 := by
      rw [← Matrix.one_mulVec v, ← Matrix.nonsing_inv_mul sigma hu, ← Matrix.mulVec_mulVec, hv',
        Matrix.mulVec_zero]
    simp [this]
  have hval : ∀ X : Mat d, (relativeEntropy X sigma).toReal
      = (cfc (fun x : ℝ => x * Real.log x) X - X * cfc Real.log sigma).trace.re := by
    intro X
    simp only [relativeEntropy, if_pos (hsupp X), EReal.toReal_coe]
  have hφA : (cfc (fun x : ℝ => x * Real.log x) rho).trace = (rho * cfc Real.log rho).trace := by
    have hfin := Matrix.finite_real_spectrum (A := rho)
    rw [cfc_mul (fun x : ℝ => x) Real.log rho (hfin.continuousOn _) (hfin.continuousOn _),
      cfc_id' ℝ rho]
  -- exact identity with the remainder
  have hid : (fun D : Mat d => (relativeEntropy (rho + D) sigma).toReal -
      (relativeEntropy rho sigma).toReal -
      (D * (1 + cfc Real.log rho - cfc Real.log sigma)).trace.re)
      = fun D : Mat d => (cfc (fun x : ℝ => x * Real.log x) (rho + D) - (rho + D) * cfc Real.log rho
          - (rho + D) + rho).trace.re := by
    funext D
    rw [hval, hval, ← Complex.sub_re, ← Complex.sub_re]
    congr 1
    simp only [Matrix.trace_add, Matrix.trace_sub, Matrix.add_mul, Matrix.mul_add, Matrix.mul_sub,
      Matrix.mul_one]
    linear_combination -hφA
  rw [hid]
  -- smallest eigenvalue of rho
  set c : ℝ := Finset.univ.inf' ⟨⟨0, hd⟩, Finset.mem_univ _⟩ hA.eigenvalues with hcdef
  have hc : 0 < c := (Finset.lt_inf'_iff _).2 fun j _ => hrho.eigenvalues_pos j
  have hev : ∀ j, c ≤ hA.eigenvalues j := fun j => Finset.inf'_le _ (Finset.mem_univ j)
  -- the trace of D * D is quadratically small
  set T : Mat d →L[ℂ] ℂ :=
    LinearMap.toContinuousLinearMap (Matrix.traceLinearMap (Fin d) ℂ ℂ) with hT
  set K : ℝ := ‖T‖
  have hQK : ∀ D : Mat d, (D * D).trace.re ≤ K * ‖D‖ ^ 2 := by
    intro D
    calc (D * D).trace.re ≤ ‖(D * D).trace‖ := Complex.re_le_norm _
      _ = ‖T (D * D)‖ := rfl
      _ ≤ K * ‖D * D‖ := T.le_opNorm _
      _ ≤ K * ‖D‖ ^ 2 := by
          rw [sq]; exact mul_le_mul_of_nonneg_left (norm_mul_le _ _) (norm_nonneg _)
  have hsmall : ∀ᶠ D : Mat d in nhds 0, K * ‖D‖ ^ 2 < c ^ 2 := by
    have ht : Filter.Tendsto (fun D : Mat d => K * ‖D‖ ^ 2) (nhds 0) (nhds 0) := by
      have hcont : Continuous (fun D : Mat d => K * ‖D‖ ^ 2) := by fun_prop
      simpa using hcont.tendsto (0 : Mat d)
    exact ht.eventually (gt_mem_nhds (by positivity))
  have hbig : (fun D : Mat d => (cfc (fun x : ℝ => x * Real.log x) (rho + D)
      - (rho + D) * cfc Real.log rho - (rho + D) + rho).trace.re)
      =O[nhdsWithin 0 {D : Mat d | D.IsHermitian}] (fun D : Mat d => ‖D‖ ^ 2) := by
    refine Asymptotics.IsBigO.of_bound (K / c) ?_
    filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds hsmall] with D hD hDs
    have hQ : (D * D).trace.re < c ^ 2 := lt_of_le_of_lt (hQK D) hDs
    have h1 := reg_main_bound hA hD hc hev hQ
    rw [Real.norm_eq_abs, norm_pow, norm_norm]
    calc _ ≤ (D * D).trace.re / c := h1
      _ ≤ K * ‖D‖ ^ 2 / c := div_le_div_of_nonneg_right (hQK D) hc.le
      _ = K / c * ‖D‖ ^ 2 := by ring
  exact hbig.trans_isLittleO
    ((Asymptotics.isLittleO_norm_pow_id one_lt_two).mono nhdsWithin_le_nhds)

end QAlgorithms.Papers.Independent.Gap48.P40

open QAlgorithms.Papers.Independent.Gap48.P40 in
theorem solution {d : ℕ} (hd : 0 < d) (rho sigma : Mat d)
    (hrho : rho.PosDef) (hsigma : sigma.PosDef) :
    (fun D : Mat d => (relativeEntropy (rho + D) sigma).toReal -
      (relativeEntropy rho sigma).toReal -
      (D * (1 + cfc Real.log rho - cfc Real.log sigma)).trace.re)
      =o[nhdsWithin 0 {D : Mat d | D.IsHermitian}] (fun D : Mat d => D) :=
  reg_main hd rho sigma hrho hsigma

end
