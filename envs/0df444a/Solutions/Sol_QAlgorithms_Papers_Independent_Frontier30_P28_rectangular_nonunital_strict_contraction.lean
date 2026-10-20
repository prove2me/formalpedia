-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Frontier30.P28.rectangular_nonunital_strict_contraction
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-20T03:01:43.264095+00:00
-- url     : https://prove2.me/submissions/6e4cefbb-9efe-4489-814a-19f75938222c

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Frontier30_P28

open scoped Matrix ComplexOrder

lemma g53_cfc_trace {n : Type} [Fintype n] [DecidableEq n] {Y : Matrix n n ℂ} (hY : Y.IsHermitian)
    (f : ℝ → ℝ) : (cfc f Y).trace = ∑ i, ((f (hY.eigenvalues i) : ℝ) : ℂ) := by
  rw [hY.cfc_eq f, Matrix.IsHermitian.cfc, Unitary.conjStarAlgAut_apply, Matrix.trace_mul_cycle,
    Unitary.star_mul_self_of_mem hY.eigenvectorUnitary.2, one_mul, Matrix.trace_diagonal]
  rfl

lemma g53_conj_eig {n : Type} [Fintype n] [DecidableEq n] {Y : Matrix n n ℂ} (hY : Y.IsHermitian) :
    star (hY.eigenvectorUnitary : Matrix n n ℂ) * Y * (hY.eigenvectorUnitary : Matrix n n ℂ) =
      Matrix.diagonal (RCLike.ofReal ∘ hY.eigenvalues) := by
  have hs := hY.spectral_theorem
  rw [Unitary.conjStarAlgAut_apply] at hs
  have hu := Unitary.star_mul_self_of_mem hY.eigenvectorUnitary.2
  generalize (hY.eigenvectorUnitary : Matrix n n ℂ) = U at *
  generalize (Matrix.diagonal (RCLike.ofReal ∘ hY.eigenvalues) : Matrix n n ℂ) = D at *
  subst hs
  calc star U * (U * D * star U) * U
      = (star U * U) * D * (star U * U) := by
        simp only [Matrix.mul_assoc]
    _ = _ := by rw [hu, one_mul, mul_one]

lemma g53_diag_cs {n : Type} [Fintype n] [DecidableEq n] (A U : Matrix n n ℂ) (hU : star U * U = 1)
    (i : n) : ‖(star U * A * U) i i‖ ^ 2 ≤ ((star U * (Aᴴ * A) * U) i i).re := by
  let a : EuclideanSpace ℂ n := WithLp.toLp 2 (fun k => U k i)
  let b : EuclideanSpace ℂ n := WithLp.toLp 2 (fun k => (A * U) k i)
  have hin : (star U * A * U) i i = inner ℂ a b := by
    rw [EuclideanSpace.inner_eq_star_dotProduct, Matrix.mul_assoc, Matrix.mul_apply]
    simp only [a, b, dotProduct, Matrix.star_apply, Pi.star_apply, RCLike.star_def]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    ring
  have hnorm : ∀ v : EuclideanSpace ℂ n, ‖v‖ ^ 2 = ∑ k, ‖v.ofLp k‖ ^ 2 := by
    intro v; rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity)]
  have ha : ‖a‖ ^ 2 = 1 := by
    rw [hnorm]
    have := congrArg (fun M => (M i i).re) hU
    simp only [Matrix.mul_apply, Matrix.star_apply, Matrix.one_apply_eq, Complex.one_re] at this
    rw [← this, Complex.re_sum]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    simp only [a, RCLike.star_def]
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, Complex.mul_re, Complex.conj_re, Complex.conj_im]
    ring
  have hb : ‖b‖ ^ 2 = ((star U * (Aᴴ * A) * U) i i).re := by
    rw [hnorm]
    have e : star U * (Aᴴ * A) * U = (A * U)ᴴ * (A * U) := by
      rw [Matrix.conjTranspose_mul, ← Matrix.star_eq_conjTranspose, ← Matrix.star_eq_conjTranspose]; simp only [Matrix.mul_assoc]
    rw [e, Matrix.mul_apply, Complex.re_sum]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    simp only [b, Matrix.conjTranspose_apply, RCLike.star_def]
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, Complex.mul_re, Complex.conj_re, Complex.conj_im]
    ring
  rw [hin, ← hb]
  have := norm_inner_le_norm (𝕜 := ℂ) a b
  have h2 : ‖inner ℂ a b‖ ^ 2 ≤ (‖a‖ * ‖b‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) this 2
  rw [mul_pow, ha, one_mul] at h2
  exact h2

lemma g53_trace_holder {n : Type} [Fintype n] [DecidableEq n] (A : Matrix n n ℂ) (q : ℝ) (hq : 1 ≤ q) :
    ‖A.trace‖ ≤ (Fintype.card n : ℝ) ^ (1 - 1/q) *
      ((cfc (fun t : ℝ => Real.rpow t (q/2)) (Aᴴ * A)).trace.re) ^ (1/q) := by
  have hP : (Aᴴ * A).PosSemidef := Matrix.posSemidef_conjTranspose_mul_self A
  have hH : (Aᴴ * A).IsHermitian := hP.isHermitian
  have hD := g53_conj_eig hH
  have hU := Unitary.star_mul_self_of_mem hH.eigenvectorUnitary.2
  have hU' := Unitary.mul_star_self_of_mem hH.eigenvectorUnitary.2
  have hlam : ∀ i, 0 ≤ hH.eigenvalues i := hP.eigenvalues_nonneg
  rw [g53_cfc_trace hH, Complex.re_sum]
  simp only [Complex.ofReal_re]
  generalize (hH.eigenvectorUnitary : Matrix n n ℂ) = U at *
  generalize hH.eigenvalues = lam at *
  have htr : A.trace = (star U * A * U).trace := by
    rw [Matrix.trace_mul_cycle, hU', one_mul]
  have hdiag : ∀ i, ‖(star U * A * U) i i‖ ≤ Real.sqrt (lam i) := by
    intro i
    have h1 := g53_diag_cs A U hU i
    rw [hD, Matrix.diagonal_apply_eq] at h1
    simp only [Function.comp] at h1
    exact Real.le_sqrt_of_sq_le h1
  have hsum : ‖A.trace‖ ≤ ∑ i, |Real.sqrt (lam i)| := by
    rw [htr, Matrix.trace]
    refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum fun i _ => ?_)
    rw [abs_of_nonneg (Real.sqrt_nonneg _)]; exact hdiag i
  have hpow := Real.rpow_sum_le_const_mul_sum_rpow Finset.univ (fun i => Real.sqrt (lam i)) hq
  have hq0 : 0 < q := by linarith
  have hS0 : 0 ≤ ∑ i, |Real.sqrt (lam i)| := Finset.sum_nonneg fun i _ => abs_nonneg _
  have hconv : ∀ i, |Real.sqrt (lam i)| ^ q = Real.rpow (lam i) (q/2) := by
    intro i
    rw [abs_of_nonneg (Real.sqrt_nonneg _), Real.sqrt_eq_rpow, ← Real.rpow_mul (hlam i)]
    congr 1; ring
  simp only [hconv, Finset.card_univ] at hpow
  have h3 : ∑ i, |Real.sqrt (lam i)| ≤ ((Fintype.card n : ℝ) ^ (q - 1) * ∑ i, Real.rpow (lam i) (q/2)) ^ (1/q) := by
    have := Real.rpow_le_rpow (Real.rpow_nonneg hS0 q) hpow (by positivity : 0 ≤ 1/q)
    rwa [← Real.rpow_mul hS0, mul_one_div_cancel hq0.ne', Real.rpow_one] at this
  have hs0 : 0 ≤ ∑ i, Real.rpow (lam i) (q/2) := Finset.sum_nonneg fun i _ => Real.rpow_nonneg (hlam i) _
  rw [Real.mul_rpow (by positivity) hs0, ← Real.rpow_mul (by positivity)] at h3
  have e : (q - 1) * (1/q) = 1 - 1/q := by field_simp
  rw [e] at h3
  exact le_trans hsum h3

open QAlgorithms in
lemma g53_specNorm_smul_one {N : ℕ} (z : ℂ) : specNorm (z • (1 : Matrix (Fin N) (Fin N) ℂ)) ≤ ‖z‖ := by
  unfold specNorm
  let _ := Matrix.instL2OpNormedAddCommGroup (m := Fin N) (n := Fin N) (𝕜 := ℂ)
  let _ := Matrix.instL2OpNormedSpace (m := Fin N) (n := Fin N) (𝕜 := ℂ)
  rw [norm_smul]
  have : ‖(1 : Matrix (Fin N) (Fin N) ℂ)‖ ≤ 1 := by
    rw [Matrix.l2_opNorm_def]
    refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun x => ?_)
    simp [Matrix.toEuclideanCLM]
  calc ‖z‖ * ‖(1 : Matrix (Fin N) (Fin N) ℂ)‖ ≤ ‖z‖ * 1 := mul_le_mul_of_nonneg_left this (norm_nonneg _)
    _ = ‖z‖ := mul_one _

open QAlgorithms.Papers.Independent.Information100.P50 (schattenNorm) in
lemma g53_schatten_scalar {N : ℕ} (p : ENNReal) (hp : p ≠ ⊤) (hq : 0 < p.toReal) (z : ℂ) :
    schattenNorm p (z • (1 : Matrix (Fin N) (Fin N) ℂ)) = (N : ℝ) ^ (1 / p.toReal) * ‖z‖ := by
  unfold schattenNorm
  rw [if_neg hp]
  have e : (z • (1 : Matrix (Fin N) (Fin N) ℂ))ᴴ * (z • 1) =
      algebraMap ℝ (Matrix (Fin N) (Fin N) ℂ) (‖z‖ ^ 2) := by
    rw [Algebra.algebraMap_eq_smul_one, Matrix.conjTranspose_smul, Matrix.conjTranspose_one,
      smul_mul_smul, mul_one]
    ext i j
    simp only [Matrix.smul_apply, Matrix.one_apply, smul_eq_mul, RCLike.star_def]
    split_ifs
    · rw [Complex.real_smul, mul_one, Complex.conj_mul']; push_cast; ring
    · simp
  rw [e, cfc_algebraMap, Algebra.algebraMap_eq_smul_one, Matrix.trace_smul, Matrix.trace_one]
  simp only [Fintype.card_fin]
  rw [Complex.real_smul, Complex.re_ofReal_mul, Complex.natCast_re]
  have hz : (‖z‖ ^ 2) ^ (p.toReal / 2) = ‖z‖ ^ p.toReal := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg _)]; congr 1; push_cast; ring
  show ((‖z‖ ^ 2) ^ (p.toReal / 2) * N) ^ (1 / p.toReal) = _
  rw [hz, Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_mul (norm_nonneg _),
    mul_one_div_cancel hq.ne', Real.rpow_one, mul_comm]

theorem g53a_entry_le_specNorm {I : Type} [Fintype I] [DecidableEq I] (M : Matrix I I ℂ) (i : I) :
    ‖M i i‖ ≤ QAlgorithms.specNorm M := by
  have h := Matrix.l2_opNorm_mulVec M (EuclideanSpace.single i (1 : ℂ))
  have h2 : ‖M i i‖ ≤ ‖(WithLp.toLp 2 (M *ᵥ (WithLp.ofLp (EuclideanSpace.single i (1 : ℂ)))) :
      EuclideanSpace ℂ I)‖ := by
    have := PiLp.norm_apply_le (p := 2) (WithLp.toLp 2 (M *ᵥ (WithLp.ofLp (EuclideanSpace.single i (1 : ℂ)))) :
      EuclideanSpace ℂ I) i
    simpa [Matrix.mulVec, dotProduct, Pi.single_apply] using this
  have h3 : ‖(EuclideanSpace.single i (1 : ℂ))‖ = 1 := by simp
  rw [h3, mul_one] at h
  exact le_trans h2 h


noncomputable section
open scoped ComplexConjugate
open QAlgorithms
attribute [local instance] Classical.decEq Classical.propDecidable
open QAlgorithms.Papers QAlgorithms.Papers.Independent QAlgorithms.Papers.Independent.Dependency50 QAlgorithms.Papers.Independent.Dependency50.P26
theorem g52b_choi_apply {I O : Type*} [Fintype I] (M : Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ)
    (o o' : O) (i i' : I) :
    outputFirstChoi M (o, i) (o', i') = M (Matrix.single i i' 1) o o' := rfl

theorem g52b_lin_expand {I O : Type*} [Fintype I] (M : Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ)
    (X : Matrix I I ℂ) : M X = ∑ i, ∑ j, X i j • M (Matrix.single i j 1) := by
  conv_lhs => rw [Matrix.matrix_eq_sum_single X]
  simp only [map_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [← map_smul, Matrix.smul_single, smul_eq_mul, mul_one]

theorem g52b_sum_psd {I ι : Type*} [Fintype I] (s : Finset ι) (A : ι → Matrix I I ℂ)
    (h : ∀ i, (A i).PosSemidef) : (∑ i ∈ s, A i).PosSemidef := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using Matrix.PosSemidef.zero
  | insert a s ha ih => rw [Finset.sum_insert ha]; exact (h a).add ih

theorem g52b_swap22 {α β γ δ : Type*} [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]
    (f : α → β → γ → δ → ℂ) :
    ∑ i, ∑ j, ∑ m, ∑ l, f i j m l = ∑ m, ∑ l, ∑ i, ∑ j, f i j m l := by
  calc ∑ i, ∑ j, ∑ m, ∑ l, f i j m l = ∑ i, ∑ m, ∑ j, ∑ l, f i j m l :=
        Finset.sum_congr rfl fun i _ => Finset.sum_comm
    _ = ∑ m, ∑ i, ∑ j, ∑ l, f i j m l := Finset.sum_comm
    _ = ∑ m, ∑ i, ∑ l, ∑ j, f i j m l :=
        Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun i _ => Finset.sum_comm
    _ = ∑ m, ∑ l, ∑ i, ∑ j, f i j m l := Finset.sum_congr rfl fun m _ => Finset.sum_comm

theorem g52b_cp_of_choi {I O : Type*} [Fintype I] [Fintype O]
    (M : Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ) (hC : (outputFirstChoi M).PosSemidef) :
    Entanglement.IsCompletelyPositive M := by
  intro r X hX
  obtain ⟨m1, v, hv⟩ := Matrix.posSemidef_iff_eq_sum_vecMulVec.mp hX
  obtain ⟨m2, g, hg⟩ := Matrix.posSemidef_iff_eq_sum_vecMulVec.mp hC
  have hMij : ∀ i j o o', M (Matrix.single i j 1) o o' =
      ∑ l, g l (o, i) * star (g l (o', j)) := by
    intro i j o o'
    rw [← g52b_choi_apply, hg, Matrix.sum_apply]
    simp [Matrix.vecMulVec_apply]
  let F : Fin m1 → Fin m2 → (Fin r × O → ℂ) := fun a l q => ∑ i, v a (q.1, i) * g l (q.2, i)
  have hY : idTensorSuperop M X = ∑ a, ∑ l, Matrix.vecMulVec (F a l) (star (F a l)) := by
    ext ⟨x, o⟩ ⟨y, o'⟩
    show M (Matrix.of fun i j => X (x, i) (y, j)) o o' = _
    rw [g52b_lin_expand]
    simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, Matrix.of_apply, hMij, hv,
      Matrix.vecMulVec_apply, Pi.star_apply, F, star_sum, star_mul']
    simp only [Finset.sum_mul_sum]
    rw [g52b_swap22]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun l _ =>
      Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [hY]
  exact g52b_sum_psd _ _ fun a => g52b_sum_psd _ _ fun l =>
    Matrix.posSemidef_vecMulVec_self_star _

end

noncomputable section
open scoped Matrix ComplexConjugate ENNReal ComplexOrder
open QAlgorithms QAlgorithms.Papers QAlgorithms.Papers.Independent QAlgorithms.Papers.Independent.Frontier30 QAlgorithms.Papers.Independent.Frontier30.P28
open QAlgorithms.Papers.Independent.Information100.P50 (M Lin schattenNorm)
open QAlgorithms.Papers.Independent.Information100.P30 (IsPositiveMap)
open QAlgorithms.Papers.Independent.Dependency50.P26 (TracePreserving)
open QAlgorithms.Papers.Independent.Dependency50.P11 (IsUnital)

theorem solution
    (n : ℕ) (hn : 2 ≤ n) (p : ℝ≥0∞) (hp : 1 < p) :
    ∃ T : Lin n (n ^ 2),
      QAlgorithms.Entanglement.IsCompletelyPositive T ∧
      TracePreserving T ∧ T (1 : M n) ≠ (1 : M (n ^ 2)) ∧
      inducedPNorm p T < 1 := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hn1 : (1 : ℝ) < n := by exact_mod_cast (by omega : 1 < n)
  set cr : ℝ := ((n : ℝ) ^ 2)⁻¹ with hcr
  have hcr0 : 0 < cr := by positivity
  set c : ℂ := (cr : ℂ) with hc
  let T : Lin n (n ^ 2) := (Matrix.traceLinearMap (Fin n) ℂ ℂ).smulRight (c • (1 : M (n ^ 2)))
  have hT : ∀ A, T A = (A.trace * c) • (1 : M (n ^ 2)) := fun A => by
    simp [T, smul_smul]
  refine ⟨T, ?_, ?_, ?_, ?_⟩
  · apply g52b_cp_of_choi
    have : QAlgorithms.Papers.Independent.Dependency50.P26.outputFirstChoi T = c • (1 : Matrix (Fin (n ^ 2) × Fin n) (Fin (n ^ 2) × Fin n) ℂ) := by
      ext ⟨o, i⟩ ⟨o', i'⟩
      rw [g52b_choi_apply, hT]
      by_cases hi : i = i'
      · subst hi
        by_cases ho : o = o' <;> simp [ho, Matrix.one_apply]
      · simp [hi, Matrix.one_apply, Matrix.trace_single_eq_of_ne _ _ _ hi]
    rw [this]
    exact Matrix.PosSemidef.one.smul (by rw [hc]; exact_mod_cast hcr0.le)
  · intro X
    rw [hT, Matrix.trace_smul, Matrix.trace_one, Fintype.card_fin, smul_eq_mul, hc, hcr]
    push_cast
    field_simp
  · intro h
    have := congrFun (congrFun h ⟨0, by positivity⟩) ⟨0, by positivity⟩
    rw [hT, Matrix.trace_one, Fintype.card_fin] at this
    simp only [Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one, hc, hcr] at this
    have h2 : ((n : ℝ) * ((n : ℝ) ^ 2)⁻¹ : ℝ) = 1 := by exact_mod_cast this
    field_simp at h2
    nlinarith
  · unfold inducedPNorm restrictedPNorm
    have hnorm_c : ‖c‖ = cr := by rw [hc, Complex.norm_real, Real.norm_of_nonneg hcr0.le]
    by_cases hpt : p = ⊤
    · subst hpt
      refine lt_of_le_of_lt (iSup_le fun A => ?_) (ENNReal.ofReal_lt_one.mpr (?_ : (n : ℝ)⁻¹ < 1))
      · apply ENNReal.ofReal_le_ofReal
        obtain ⟨A, -, hA⟩ := A
        simp only [schattenNorm, if_pos rfl] at hA ⊢
        rw [hT]
        refine le_trans (g53_specNorm_smul_one _) ?_
        rw [norm_mul, hnorm_c]
        have htr : ‖A.trace‖ ≤ n * specNorm A := by
          rw [Matrix.trace]
          refine le_trans (norm_sum_le _ _) ?_
          calc ∑ i, ‖A.diag i‖ ≤ ∑ _i : Fin n, specNorm A :=
                Finset.sum_le_sum fun i _ => g53a_entry_le_specNorm A i
            _ = n * specNorm A := by simp
        calc ‖A.trace‖ * cr ≤ (n * 1) * cr := by
              apply mul_le_mul_of_nonneg_right _ hcr0.le
              exact le_trans htr (mul_le_mul_of_nonneg_left hA hn0.le)
          _ = (n : ℝ)⁻¹ := by rw [hcr]; field_simp
      · exact inv_lt_one_of_one_lt₀ hn1
    · set q := p.toReal with hqdef
      have hq1 : 1 < q := by
        have := ENNReal.toReal_strict_mono hpt hp
        simpa using this
      have hq0 : 0 < q := by linarith
      have hβ : (n : ℝ) ^ (1 / q - 1) < 1 :=
        Real.rpow_lt_one_of_one_lt_of_neg hn1 (by
          have : 1 / q < 1 := by rw [div_lt_one hq0]; exact hq1
          linarith)
      refine lt_of_le_of_lt (iSup_le fun A => ?_) (ENNReal.ofReal_lt_one.mpr hβ)
      apply ENNReal.ofReal_le_ofReal
      obtain ⟨A, -, hA⟩ := A
      rw [hT, g53_schatten_scalar p hpt (by rw [← hqdef]; exact hq0), ← hqdef, norm_mul, hnorm_c]
      have hH := g53_trace_holder A q hq1.le
      have hA' : ((cfc (fun t : ℝ => Real.rpow t (q / 2)) (Aᴴ * A)).trace.re) ^ (1 / q) ≤ 1 := by
        simp only [schattenNorm, if_neg hpt, ← hqdef] at hA
        exact hA
      rw [Fintype.card_fin] at hH
      have htr : ‖A.trace‖ ≤ (n : ℝ) ^ (1 - 1 / q) := by
        refine le_trans hH ?_
        calc (n : ℝ) ^ (1 - 1 / q) * _ ≤ (n : ℝ) ^ (1 - 1 / q) * 1 :=
              mul_le_mul_of_nonneg_left hA' (by positivity)
          _ = _ := mul_one _
      calc ((n ^ 2 : ℕ) : ℝ) ^ (1 / q) * (‖A.trace‖ * cr)
          ≤ ((n ^ 2 : ℕ) : ℝ) ^ (1 / q) * ((n : ℝ) ^ (1 - 1 / q) * cr) := by
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            exact mul_le_mul_of_nonneg_right htr hcr0.le
        _ = (n : ℝ) ^ (1 / q - 1) := by
            have e1 : ((n ^ 2 : ℕ) : ℝ) ^ (1 / q) = (n : ℝ) ^ (2 / q) := by
              rw [Nat.cast_pow, ← Real.rpow_natCast, ← Real.rpow_mul hn0.le]; congr 1; push_cast; ring
            have e2 : cr = (n : ℝ) ^ (-2 : ℝ) := by
              rw [hcr, Real.rpow_neg hn0.le]; norm_cast
            rw [e1, e2, ← mul_assoc, ← Real.rpow_add hn0, ← Real.rpow_add hn0]
            congr 1; ring
