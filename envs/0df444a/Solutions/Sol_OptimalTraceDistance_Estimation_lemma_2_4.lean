-- Prove2me | solution 1 for OptimalTraceDistance.Estimation.lemma_2_4
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-22T21:26:56.034637+00:00
-- url     : https://prove2.me/submissions/29dc2152-1150-4e9c-9f0a-b4538edf0379

import Theorems.Thm_OptimalTraceDistance_Estimation_lemma_2_3
import Theorems.Thm_MatrixSpectral_eigenvalue_count_le_add_rank

open MeasureTheory
open scoped BigOperators Matrix Classical ENNReal ComplexOrder
noncomputable section

namespace OTDLemma24
open Matrix OptimalTraceDistance.Estimation

variable {d : ℕ}

/-- quadratic form of a conjugated matrix -/
lemma quad_conj (U : Mat d) (B : Mat d) (x : Fin d → ℂ) :
    star x ⬝ᵥ ((U * B * star U) *ᵥ x) = star (star U *ᵥ x) ⬝ᵥ (B *ᵥ (star U *ᵥ x)) := by
  rw [← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec, star_mulVec]
  simp [Matrix.star_eq_conjTranspose]

lemma quad_diag (w : Fin d → ℂ) (y : Fin d → ℂ) :
    star y ⬝ᵥ (diagonal w *ᵥ y) = ∑ i, w i * (star (y i) * y i) := by
  simp only [dotProduct, mulVec_diagonal, Pi.star_apply]
  refine Finset.sum_congr rfl (fun i _ => by ring)

lemma quad_cfc {A : Mat d} (hA : A.IsHermitian) (f : ℝ → ℝ) (x : Fin d → ℂ) :
    star x ⬝ᵥ (cfc f A *ᵥ x) =
      ∑ i, ((f (hA.eigenvalues i) : ℝ) : ℂ) *
        (star ((star (hA.eigenvectorUnitary : Mat d) *ᵥ x) i) *
          ((star (hA.eigenvectorUnitary : Mat d) *ᵥ x) i)) := by
  rw [hA.cfc_eq, IsHermitian.cfc, Unitary.conjStarAlgAut_apply, quad_conj, quad_diag]
  rfl

lemma unitary_norm (U : Mat d) (hU : U ∈ unitary (Mat d)) (x : Fin d → ℂ) :
    star (star U *ᵥ x) ⬝ᵥ (star U *ᵥ x) = star x ⬝ᵥ x := by
  have := quad_conj U 1 x
  rw [mul_one, Unitary.mul_star_self_of_mem hU, one_mulVec, one_mulVec] at this
  exact this.symm

lemma sum_normsq (y : Fin d → ℂ) : star y ⬝ᵥ y = ∑ i, ((‖y i‖^2 : ℝ) : ℂ) := by
  simp only [dotProduct, Pi.star_apply]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [mul_comm]
  show y i * (starRingEnd ℂ) (y i) = _
  rw [Complex.mul_conj', Complex.ofReal_pow]


lemma inner_eq (A : Mat d) (x : EuclideanSpace ℂ (Fin d)) :
    RCLike.re (inner ℂ (Matrix.toEuclideanCLM (𝕜 := ℂ) A x) x) =
      (star (WithLp.ofLp x) ⬝ᵥ (A *ᵥ WithLp.ofLp x)).re := by
  rw [EuclideanSpace.inner_eq_star_dotProduct, Matrix.ofLp_toEuclideanCLM]
  simp only [dotProduct, Pi.star_apply, RCLike.re_to_complex, Complex.re_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  simp only [Complex.mul_re, Complex.star_def, Complex.conj_re, Complex.conj_im]
  ring

lemma normsq_eq (x : EuclideanSpace ℂ (Fin d)) :
    ‖x‖^2 = (star (WithLp.ofLp x) ⬝ᵥ (WithLp.ofLp x)).re := by
  rw [← inner_self_eq_norm_sq (𝕜 := ℂ), EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm]
  rfl

lemma opNorm_le_of_quad {A : Mat d} (hA : A.IsHermitian) {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ x : Fin d → ℂ, |(star x ⬝ᵥ (A *ᵥ x)).re| ≤ c * (star x ⬝ᵥ x).re) :
    opNorm A ≤ c := by
  unfold opNorm
  have hT : (Matrix.toEuclideanCLM (𝕜 := ℂ) A : EuclideanSpace ℂ (Fin d) →ₗ[ℂ] _).IsSymmetric := by
    rw [Matrix.coe_toEuclideanCLM_eq_toEuclideanLin]
    exact Matrix.isSymmetric_toEuclideanLin_iff.mpr hA
  rw [ContinuousLinearMap.norm_eq_iSup_rayleighQuotient _ hT]
  refine ciSup_le (fun x => ?_)
  simp only [ContinuousLinearMap.rayleighQuotient, ContinuousLinearMap.reApplyInnerSelf]
  rw [inner_eq, normsq_eq]
  rcases eq_or_lt_of_le (sq_nonneg ‖x‖) with h0 | hpos
  · rw [normsq_eq] at h0; rw [← h0]; simp [hc]
  · rw [normsq_eq] at hpos
    rw [abs_div, abs_of_pos hpos, div_le_iff₀ hpos]
    exact h _

lemma quad_le_opNorm (A : Mat d) (x : Fin d → ℂ) :
    |(star x ⬝ᵥ (A *ᵥ x)).re| ≤ opNorm A * (star x ⬝ᵥ x).re := by
  have := ContinuousLinearMap.rayleighQuotient_le_norm (Matrix.toEuclideanCLM (𝕜 := ℂ) A)
    (WithLp.toLp 2 x)
  simp only [ContinuousLinearMap.rayleighQuotient, ContinuousLinearMap.reApplyInnerSelf] at this
  rw [inner_eq, normsq_eq] at this
  simp only [WithLp.ofLp_toLp] at this
  rcases eq_or_lt_of_le (show 0 ≤ (star x ⬝ᵥ x).re from by
      rw [sum_normsq]; simp only [Complex.re_sum, Complex.ofReal_re]; positivity) with h0 | hpos
  · have hx : x = 0 := by
      have := (h0.symm)
      rw [sum_normsq] at this
      simp only [Complex.re_sum, Complex.ofReal_re] at this
      have h2 := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg ‖x i‖)).mp this
      funext i; have := h2 i (Finset.mem_univ i); simpa using this
    subst hx; simp
  · rw [abs_div, abs_of_pos hpos, div_le_iff₀ hpos] at this
    exact this


section spectral
variable {A : Mat d} (hA : A.IsHermitian)
include hA

lemma U_mem : (hA.eigenvectorUnitary : Mat d) ∈ unitary (Mat d) := (hA.eigenvectorUnitary).2

lemma cfc_explicit (f : ℝ → ℝ) : cfc f A =
    (hA.eigenvectorUnitary : Mat d) * diagonal (fun i => ((f (hA.eigenvalues i) : ℝ) : ℂ)) *
      star (hA.eigenvectorUnitary : Mat d) := by
  rw [hA.cfc_eq, IsHermitian.cfc, Unitary.conjStarAlgAut_apply]; rfl

lemma cfc_mul' (f g : ℝ → ℝ) : cfc f A * cfc g A = cfc (fun t => f t * g t) A := by
  rw [cfc_explicit hA, cfc_explicit hA, cfc_explicit hA]
  set U := (hA.eigenvectorUnitary : Mat d)
  have hU : star U * U = 1 := Unitary.star_mul_self_of_mem (U_mem hA)
  calc U * diagonal (fun i => ((f (hA.eigenvalues i) : ℝ) : ℂ)) * star U *
        (U * diagonal (fun i => ((g (hA.eigenvalues i) : ℝ) : ℂ)) * star U)
      = U * diagonal (fun i => ((f (hA.eigenvalues i) : ℝ) : ℂ)) * (star U * U) *
          diagonal (fun i => ((g (hA.eigenvalues i) : ℝ) : ℂ)) * star U := by
        simp only [Matrix.mul_assoc]
    _ = _ := by rw [hU, Matrix.mul_one, Matrix.mul_assoc U, diagonal_mul_diagonal]; push_cast; rfl

lemma cfc_congr' {f g : ℝ → ℝ} (h : ∀ i, f (hA.eigenvalues i) = g (hA.eigenvalues i)) :
    cfc f A = cfc g A := by
  rw [cfc_explicit hA, cfc_explicit hA]; simp only [h]

lemma cfc_one' : cfc (fun _ => (1:ℝ)) A = 1 := by
  rw [cfc_explicit hA]; simp only [Complex.ofReal_one]
  rw [diagonal_one, Matrix.mul_one, Unitary.mul_star_self_of_mem (U_mem hA)]

lemma cfc_id'' : cfc (fun t : ℝ => t) A = A := cfc_id' ℝ A hA.isSelfAdjoint

lemma cfc_herm (f : ℝ → ℝ) : (cfc f A).IsHermitian := by
  rw [cfc_explicit hA]
  exact isHermitian_mul_mul_conjTranspose _
    (isHermitian_diagonal_of_self_adjoint _ (funext fun i => by simp [Complex.conj_ofReal]))

lemma trace_cfc (f : ℝ → ℝ) : (cfc f A).trace = ∑ i, ((f (hA.eigenvalues i) : ℝ) : ℂ) := by
  rw [cfc_explicit hA, Matrix.trace_mul_cycle, Unitary.star_mul_self_of_mem (U_mem hA),
    Matrix.one_mul, trace_diagonal]

lemma quad_re (f : ℝ → ℝ) (x : Fin d → ℂ) :
    (star x ⬝ᵥ (cfc f A *ᵥ x)).re =
      ∑ i, f (hA.eigenvalues i) * ‖(star (hA.eigenvectorUnitary : Mat d) *ᵥ x) i‖^2 := by
  rw [quad_cfc hA, Complex.re_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [mul_comm (star _), show star ((star (hA.eigenvectorUnitary : Mat d) *ᵥ x) i) =
    (starRingEnd ℂ) ((star (hA.eigenvectorUnitary : Mat d) *ᵥ x) i) from rfl, Complex.mul_conj',
    ← Complex.ofReal_pow, ← Complex.ofReal_mul, Complex.ofReal_re]

lemma quad_re_self (x : Fin d → ℂ) :
    (star x ⬝ᵥ (A *ᵥ x)).re =
      ∑ i, hA.eigenvalues i * ‖(star (hA.eigenvectorUnitary : Mat d) *ᵥ x) i‖^2 := by
  conv_lhs => rw [← cfc_id'' hA]
  exact quad_re hA _ x

lemma sum_normsq_U (x : Fin d → ℂ) :
    ∑ i, ‖(star (hA.eigenvectorUnitary : Mat d) *ᵥ x) i‖^2 = (star x ⬝ᵥ x).re := by
  rw [← unitary_norm _ (U_mem hA) x, sum_normsq, Complex.re_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Complex.ofReal_re]

end spectral

lemma normsq_nonneg (x : Fin d → ℂ) : 0 ≤ (star x ⬝ᵥ x).re := by
  rw [sum_normsq, Complex.re_sum]; simp only [Complex.ofReal_re]; positivity


lemma trace_cfc_sq {A : Mat d} (hA : A.IsHermitian) (h : ℝ → ℝ) :
    (cfc h (Aᴴ * A)).trace.re = ∑ i, h (hA.eigenvalues i ^ 2) := by
  have e : Aᴴ * A = cfc (fun t : ℝ => t * t) A := by
    rw [hA.eq, ← cfc_mul' hA, cfc_id'' hA]
  have hfin : (spectrum ℝ A).Finite := Matrix.finite_real_spectrum
  rw [e, ← cfc_comp h (fun t : ℝ => t * t) A hA.isSelfAdjoint
    ((hfin.image _).continuousOn _) (hfin.continuousOn _), trace_cfc hA, Complex.re_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  simp [sq]

lemma mulVec_col (A B : Mat d) (k j : Fin d) : (A *ᵥ fun i => B i k) j = (A * B) j k := by
  simp [mulVec, dotProduct, mul_apply]

lemma col_normsq (B : Mat d) (k : Fin d) :
    star (fun i => B i k) ⬝ᵥ (fun i => B i k) = (star B * B) k k := by
  simp [dotProduct, mul_apply, Matrix.star_eq_conjTranspose]


/-! ### Eigenvalue facts -/

lemma eig_quad {A : Mat d} (hA : A.IsHermitian) (k : Fin d) :
    (star (fun i => (hA.eigenvectorUnitary : Mat d) i k) ⬝ᵥ
      (A *ᵥ (fun i => (hA.eigenvectorUnitary : Mat d) i k))).re = hA.eigenvalues k ∧
    (star (fun i => (hA.eigenvectorUnitary : Mat d) i k) ⬝ᵥ
      (fun i => (hA.eigenvectorUnitary : Mat d) i k)).re = 1 := by
  have hVV : star (hA.eigenvectorUnitary : Mat d) * (hA.eigenvectorUnitary : Mat d) = 1 :=
    Unitary.star_mul_self_of_mem (U_mem hA)
  constructor
  · rw [quad_re_self hA]
    simp only [mulVec_col]
    rw [hVV, Finset.sum_eq_single k]
    · simp
    · intro i _ hi; simp [one_apply_ne hi]
    · simp
  · rw [col_normsq, hVV]; simp

lemma eig_abs_le {A : Mat d} (hA : A.IsHermitian) (k : Fin d) :
    |hA.eigenvalues k| ≤ opNorm A := by
  obtain ⟨h1, h2⟩ := eig_quad hA k
  have := quad_le_opNorm A (fun i => (hA.eigenvectorUnitary : Mat d) i k)
  rwa [h1, h2, mul_one] at this

lemma matrixEval_eq_aeval (p : Polynomial ℝ) (A : Mat d) :
    matrixEval p A = Polynomial.aeval A p := by
  rw [Polynomial.aeval_def, Polynomial.eval₂_eq_sum, matrixEval, Polynomial.sum_def]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul]
  rw [show ((p.coeff k : ℝ) : ℂ) • A ^ k = (p.coeff k : ℝ) • A ^ k from
    (RCLike.real_smul_eq_coe_smul (K := ℂ) _ _).symm]

lemma traceError_eq (K : ℕ) (s : ℝ) {A : Mat d} (hA : A.IsHermitian) :
    traceError K s A = ∑ k, (|hA.eigenvalues k| - (qScaled K s).eval (hA.eigenvalues k)) := by
  unfold traceError tr absMat
  rw [trace_sub, Complex.sub_re, trace_cfc_sq hA, matrixEval_eq_aeval,
    ← cfc_polynomial (qScaled K s) A hA.isSelfAdjoint, trace_cfc hA, Complex.re_sum,
    ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [Real.sqrt_sq_eq_abs, Complex.ofReal_re]


/-! ### Scalar integrals -/

lemma sign_monotone : Monotone sign := by
  intro a b hab
  rcases lt_trichotomy a 0 with ha | rfl | ha
  · have : sign a = -1 := by simp [sign, ha]
    rw [this]; unfold sign; split_ifs <;> norm_num
  · rcases lt_trichotomy b 0 with hb | rfl | hb
    · linarith
    · exact le_rfl
    · simp [sign, hb, not_lt.mpr hb.le, hb.ne']
  · have hb : 0 < b := lt_of_lt_of_le ha hab
    simp [sign, not_lt.mpr ha.le, ha.ne', not_lt.mpr hb.le, hb.ne']

lemma sign_intInt (a b : ℝ) : IntervalIntegrable sign volume a b :=
  sign_monotone.intervalIntegrable

lemma int_sign (x : ℝ) : ∫ t in (0:ℝ)..x, sign t = |x| := by
  rcases le_or_gt 0 x with hx | hx
  · rw [intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hx (f := fun t => t)
      continuousOn_id (fun t ht => ?_) (sign_intInt 0 x)]
    · simp [abs_of_nonneg hx]
    · have : sign t = 1 := by unfold sign; simp [not_lt.mpr ht.1.le, ht.1.ne']
      rw [this]; exact hasDerivAt_id t
  · rw [intervalIntegral.integral_symm, intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hx.le
      (f := fun t => -t) continuousOn_neg (fun t ht => ?_) (sign_intInt x 0)]
    · simp [abs_of_neg hx]
    · have : sign t = -1 := by unfold sign; simp [ht.2]
      rw [this]; exact (hasDerivAt_id t).neg

lemma qScaled_deriv (K : ℕ) {s : ℝ} (hs : s ≠ 0) (t : ℝ) :
    (qScaled K s).derivative.eval t = (q K).derivative.eval (t/s) := by
  simp only [qScaled, Polynomial.derivative_mul, Polynomial.derivative_C, zero_mul, zero_add,
    Polynomial.derivative_comp, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_comp,
    Polynomial.derivative_X, mul_one, Polynomial.eval_X]
  rw [div_eq_inv_mul]; field_simp

lemma int_qprime (K : ℕ) {s : ℝ} (hs : s ≠ 0) (hq0 : (q K).eval 0 = 0) (x : ℝ) :
    ∫ t in (0:ℝ)..x, (q K).derivative.eval (t/s) = (qScaled K s).eval x := by
  have : (fun t => (q K).derivative.eval (t/s)) = fun t => (qScaled K s).derivative.eval t := by
    funext t; rw [qScaled_deriv K hs]
  rw [this, intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t _ => Polynomial.hasDerivAt (qScaled K s) t)]
  · simp [qScaled, Polynomial.eval_comp, hq0]
  · exact (Polynomial.continuous _).intervalIntegrable _ _

def gfun (K : ℕ) (s : ℝ) (t : ℝ) : ℝ := sign t - (q K).derivative.eval (t/s)

lemma gfun_intInt (K : ℕ) (s : ℝ) (a b : ℝ) : IntervalIntegrable (gfun K s) volume a b :=
  (sign_intInt a b).sub
    ((by fun_prop : Continuous fun t => (q K).derivative.eval (t/s)).intervalIntegrable _ _)

lemma e_eq (K : ℕ) {s : ℝ} (hs : s ≠ 0) (hq0 : (q K).eval 0 = 0) (x : ℝ) :
    |x| - (qScaled K s).eval x =
      (∫ t in (-s)..x, gfun K s t) - ∫ t in (-s)..0, gfun K s t := by
  rw [intervalIntegral.integral_interval_sub_left (gfun_intInt K s _ _) (gfun_intInt K s _ _)]
  unfold gfun
  rw [intervalIntegral.integral_sub (sign_intInt 0 x)
    ((by fun_prop : Continuous fun t => (q K).derivative.eval (t/s)).intervalIntegrable _ _),
    int_sign, int_qprime K hs hq0]

lemma F_indicator (K : ℕ) {s x : ℝ} (hx : x ∈ Set.Icc (-s) s) :
    ∫ t in (-s)..x, gfun K s t = ∫ t in (-s)..s, Set.indicator {t | t ≤ x} (gfun K s) t :=
  (intervalIntegral.integral_indicator hx).symm


lemma ind_intInt (K : ℕ) (s a b x : ℝ) :
    IntervalIntegrable (Set.indicator {t | t ≤ x} (gfun K s)) volume a b := by
  have h := gfun_intInt K s a b
  exact ⟨h.1.indicator measurableSet_Iic, h.2.indicator measurableSet_Iic⟩

lemma sum_intInt {a b : ℝ} (f : Fin d → ℝ → ℝ)
    (hf : ∀ k, IntervalIntegrable (f k) volume a b) :
    IntervalIntegrable (fun t => ∑ k, f k t) volume a b := by
  suffices h : ∀ S : Finset (Fin d), IntervalIntegrable (fun t => ∑ k ∈ S, f k t) volume a b from
    h Finset.univ
  intro S
  induction S using Finset.induction_on with
  | empty => simp
  | insert k S hk ih =>
    simp only [Finset.sum_insert hk]
    exact (hf k).add ih

lemma sum_ind (K : ℕ) (s : ℝ) (lam : Fin d → ℝ) (t : ℝ) :
    ∑ k, Set.indicator {t | t ≤ lam k} (gfun K s) t =
      gfun K s t * ((Finset.univ.filter (fun k => t ≤ lam k)).card : ℝ) := by
  simp only [Set.indicator_apply, Set.mem_ofPred_eq]
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul, mul_comm]

lemma sumF (K : ℕ) {s : ℝ} (lam : Fin d → ℝ) (hlam : ∀ k, lam k ∈ Set.Icc (-s) s) :
    ∑ k, ∫ t in (-s)..(lam k), gfun K s t =
      ∫ t in (-s)..s, gfun K s t * ((Finset.univ.filter (fun k => t ≤ lam k)).card : ℝ) := by
  simp only [F_indicator K (hlam _)]
  rw [← intervalIntegral.integral_finsetSum (fun k _ => ind_intInt K s _ _ _)]
  simp only [sum_ind]

lemma sign_mul_pos {s : ℝ} (hs : 0 < s) (x : ℝ) : sign (s * x) = sign x := by
  unfold sign
  rcases lt_trichotomy x 0 with h | rfl | h
  · simp [h, mul_neg_of_pos_of_neg hs h]
  · simp
  · simp [not_lt.mpr h.le, h.ne', not_lt.mpr (mul_pos hs h).le, (mul_pos hs h).ne']

lemma int_abs_g (K : ℕ) {s : ℝ} (hs : 0 < s) :
    ∫ t in (-s)..s, |gfun K s t| = s * ∫ x in (-1:ℝ)..1, |sign x - (q K).derivative.eval x| := by
  have h := intervalIntegral.integral_comp_mul_left (fun t => |gfun K s t|) (a := -1) (b := 1)
    hs.ne'
  simp only [mul_neg, mul_one, smul_eq_mul] at h
  have e : (fun x => |gfun K s (s * x)|) = fun x => |sign x - (q K).derivative.eval x| := by
    funext x; unfold gfun; rw [sign_mul_pos hs, mul_div_cancel_left₀ _ hs.ne']
  rw [e] at h
  rw [h]; field_simp

end OTDLemma24

open OptimalTraceDistance.Estimation OTDLemma24

theorem solution : ∃ C : ℝ, 0 < C ∧ ∀ (d K : ℕ), 0 < d → 2 ≤ K →
  ∀ s : ℝ, 0 < s → ∀ U V : Mat d, U.IsHermitian → V.IsHermitian →
    opNorm U ≤ s → opNorm V ≤ s →
    |traceError K s U - traceError K s V| ≤ C*s/(K : ℝ) * (U-V).rank := by
  refine ⟨64, by norm_num, fun d K hd hK s hs U V hU hV hUs hVs => ?_⟩
  obtain ⟨-, -, hq0, -, -, hint, hle, -⟩ := lemma_2_3 K hK
  have hsne : s ≠ 0 := hs.ne'
  have hmemU : ∀ k, hU.eigenvalues k ∈ Set.Icc (-s) s := fun k => by
    have := (eig_abs_le hU k).trans hUs; rw [abs_le] at this; exact this
  have hmemV : ∀ k, hV.eigenvalues k ∈ Set.Icc (-s) s := fun k => by
    have := (eig_abs_le hV k).trans hVs; rw [abs_le] at this; exact this
  set F0 := ∫ t in (-s)..0, gfun K s t
  have hTU : traceError K s U = (∑ k, ∫ t in (-s)..(hU.eigenvalues k), gfun K s t) - d * F0 := by
    rw [traceError_eq K s hU]
    simp only [e_eq K hsne hq0, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
    rfl
  have hTV : traceError K s V = (∑ k, ∫ t in (-s)..(hV.eigenvalues k), gfun K s t) - d * F0 := by
    rw [traceError_eq K s hV]
    simp only [e_eq K hsne hq0, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
    rfl
  set cU : ℝ → ℝ := fun t => ((Finset.univ.filter (fun k => t ≤ hU.eigenvalues k)).card : ℝ)
  set cV : ℝ → ℝ := fun t => ((Finset.univ.filter (fun k => t ≤ hV.eigenvalues k)).card : ℝ)
  set r : ℝ := ((U - V).rank : ℝ)
  have hc : ∀ t, |cU t - cV t| ≤ r := by
    intro t
    have h1 := (MatrixSpectral.eigenvalue_count_le_add_rank U V hU hV t).2
    have h2 := (MatrixSpectral.eigenvalue_count_le_add_rank V U hV hU t).2
    have hr : (V - U).rank = (U - V).rank := by
      rw [show V - U = (-1 : ℂ) • (U - V) by rw [neg_one_smul]; abel]
      exact Matrix.rank_smul_of_mem_nonZeroDivisors _ (mem_nonZeroDivisors_of_ne_zero (by norm_num))
    rw [hr] at h2
    rw [abs_le]; constructor
    · have : (cV t) ≤ cU t + r := by simp only [cU, cV, r]; exact_mod_cast h2
      linarith
    · have : (cU t) ≤ cV t + r := by simp only [cU, cV, r]; exact_mod_cast h1
      linarith
  have hIU : IntervalIntegrable (fun t => gfun K s t * cU t) volume (-s) s := by
    have hsum : IntervalIntegrable (fun t => ∑ k, Set.indicator {t | t ≤ hU.eigenvalues k}
        (gfun K s) t) volume (-s) s :=
      sum_intInt _ (fun k => ind_intInt K s (-s) s (hU.eigenvalues k))
    simpa only [sum_ind] using hsum
  have hIV : IntervalIntegrable (fun t => gfun K s t * cV t) volume (-s) s := by
    have hsum : IntervalIntegrable (fun t => ∑ k, Set.indicator {t | t ≤ hV.eigenvalues k}
        (gfun K s) t) volume (-s) s :=
      sum_intInt _ (fun k => ind_intInt K s (-s) s (hV.eigenvalues k))
    simpa only [sum_ind] using hsum
  have hdiff : traceError K s U - traceError K s V =
      ∫ t in (-s)..s, (gfun K s t * cU t - gfun K s t * cV t) := by
    rw [hTU, hTV, sumF K _ hmemU, sumF K _ hmemV, intervalIntegral.integral_sub hIU hIV]
    ring
  have hgabs : IntervalIntegrable (fun t => |gfun K s t|) volume (-s) s :=
    (gfun_intInt K s (-s) s).abs
  rw [hdiff]
  have hss : -s ≤ s := by linarith
  calc |∫ t in (-s)..s, (gfun K s t * cU t - gfun K s t * cV t)|
      ≤ ∫ t in (-s)..s, |gfun K s t * cU t - gfun K s t * cV t| :=
        intervalIntegral.abs_integral_le_integral_abs hss
    _ ≤ ∫ t in (-s)..s, r * |gfun K s t| := by
        refine intervalIntegral.integral_mono_on hss (hIU.sub hIV).abs (hgabs.const_mul r)
          (fun t _ => ?_)
        rw [← mul_sub, abs_mul, mul_comm r]
        exact mul_le_mul_of_nonneg_left (hc t) (abs_nonneg _)
    _ = r * (s * ∫ x in (-1:ℝ)..1, |sign x - (q K).derivative.eval x|) := by
        rw [intervalIntegral.integral_const_mul, int_abs_g K hs]
    _ ≤ r * (s * (64 / K)) := by
        gcongr
    _ = 64 * s / K * r := by ring
