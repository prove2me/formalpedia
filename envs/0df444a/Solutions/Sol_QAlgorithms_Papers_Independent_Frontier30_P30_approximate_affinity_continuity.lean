-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Frontier30.P30.approximate_affinity_continuity
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-20T02:36:05.249202+00:00
-- url     : https://prove2.me/submissions/fe121886-801c-4cc5-b6b8-8e5ac3adff36

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Frontier30_P30

open scoped Matrix ComplexOrder MatrixOrder

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

lemma g53_posPart_aux {n : Type} [Fintype n] [DecidableEq n] {A B U : Matrix n n ℂ} (lam : n → ℝ)
    (hA : A.PosSemidef) (hB : B.PosSemidef) (hU : U * star U = 1)
    (hD : star U * (A - B) * U = Matrix.diagonal (RCLike.ofReal ∘ lam)) :
    ∑ i, max (lam i) 0 ≤ A.trace.re := by
  have hA' := hA.conjTranspose_mul_mul_same U
  have hB' := hB.conjTranspose_mul_mul_same U
  have htr : A.trace = (Uᴴ * A * U).trace := by
    rw [Matrix.trace_mul_cycle, ← Matrix.star_eq_conjTranspose, hU, one_mul]
  rw [htr, Matrix.trace, Complex.re_sum]
  apply Finset.sum_le_sum
  intro i _
  have h1 : (Uᴴ * A * U) i i - (Uᴴ * B * U) i i = ((lam i : ℝ) : ℂ) := by
    have := congrArg (fun M => M i i) hD
    rw [Matrix.mul_sub, Matrix.sub_mul] at this
    simpa [Matrix.star_eq_conjTranspose] using this
  have ha' : 0 ≤ ((Uᴴ * A * U) i i).re := (Complex.nonneg_iff.mp (hA'.diag_nonneg (i := i))).1
  have hb' : 0 ≤ ((Uᴴ * B * U) i i).re := (Complex.nonneg_iff.mp (hB'.diag_nonneg (i := i))).1
  have h2 := congrArg Complex.re h1
  simp only [Complex.sub_re, Complex.ofReal_re] at h2
  simp only [Matrix.diag]
  exact max_le (by linarith) ha'

lemma g53_parts {n : Type} [Fintype n] [DecidableEq n] (X : Matrix n n ℂ) (hX : X.IsHermitian) :
    cfc (fun t : ℝ => max t 0) X - cfc (fun t : ℝ => max (-t) 0) X = X := by
  have hsa : IsSelfAdjoint X := hX.isSelfAdjoint
  rw [← cfc_sub (fun t : ℝ => max t 0) (fun t : ℝ => max (-t) 0) X]
  conv_rhs => rw [← cfc_id ℝ X]
  apply cfc_congr
  intro t _
  simp only [id]
  rcases le_total t 0 with h | h <;> simp [h]

lemma g53_cfc_psd {n : Type} [Fintype n] [DecidableEq n] (X : Matrix n n ℂ) (f : ℝ → ℝ)
    (hf : ∀ t, 0 ≤ f t) : (cfc f X).PosSemidef := by
  rw [← Matrix.nonneg_iff_posSemidef]
  exact cfc_nonneg (fun t _ => hf t)

lemma g53_posPart_le {n : Type} [Fintype n] [DecidableEq n] {Y A B : Matrix n n ℂ} (hY : Y.IsHermitian)
    (hA : A.PosSemidef) (hB : B.PosSemidef) (hYAB : Y = A - B) :
    (cfc (fun t : ℝ => max t 0) Y).trace.re ≤ A.trace.re := by
  rw [g53_cfc_trace hY, Complex.re_sum]
  simp only [Complex.ofReal_re]
  have hD := g53_conj_eig hY
  have hu := Unitary.mul_star_self_of_mem hY.eigenvectorUnitary.2
  generalize (hY.eigenvectorUnitary : Matrix n n ℂ) = U at *
  generalize hY.eigenvalues = lam at *
  subst hYAB
  exact g53_posPart_aux lam hA hB hu hD

lemma g53_traceNorm_herm {n : Type} [Fintype n] [DecidableEq n] {X : Matrix n n ℂ} (hX : X.IsHermitian) :
    QAlgorithms.traceNorm X =
      (cfc (fun t : ℝ => max t 0) X).trace.re + (cfc (fun t : ℝ => max (-t) 0) X).trace.re := by
  have hsa : IsSelfAdjoint X := hX.isSelfAdjoint
  unfold QAlgorithms.traceNorm
  rw [hX.eq]
  have h1 : X * X = cfc (fun t : ℝ => t * t) X := by
    rw [cfc_mul (fun t : ℝ => t) (fun t : ℝ => t) X, cfc_id' ℝ X]
  rw [h1, ← cfc_comp Real.sqrt (fun t : ℝ => t * t) X, ← Complex.add_re, ← Matrix.trace_add,
    ← cfc_add X (fun t : ℝ => max t 0) (fun t : ℝ => max (-t) 0)]
  congr 2
  apply cfc_congr
  intro t _
  simp only [Function.comp]
  rw [← sq, Real.sqrt_sq_eq_abs]
  rcases le_total t 0 with h | h
  · rw [abs_of_nonpos h]; simp [h]
  · rw [abs_of_nonneg h]; simp [h]

lemma g53_real_aff (A B U V W c M L ε p : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) (hp : p * (1 + ε) = 1)
    (hc : 0 ≤ c) (h1 : |p * A + (1 - p) * V - W| ≤ c) (h2 : |p * B + (1 - p) * U - W| ≤ c)
    (hU : |U| ≤ M * L) (hV : |V| ≤ M * L) : |A - B| ≤ M * (2 * ε) * L + 4 * c := by
  have hq : (1 - p) * (1 + ε) = ε := by linarith
  have e1 := abs_le.mp h1; have e2 := abs_le.mp h2
  have eU := abs_le.mp hU; have eV := abs_le.mp hV
  have k := (by linarith : (0:ℝ) ≤ 1 + ε)
  have a1 := mul_le_mul_of_nonneg_left e1.2 k
  have a2 := mul_le_mul_of_nonneg_left e1.1 k
  have a3 := mul_le_mul_of_nonneg_left e2.2 k
  have a4 := mul_le_mul_of_nonneg_left e2.1 k
  have b1 := mul_le_mul_of_nonneg_left eU.2 hε.le
  have b2 := mul_le_mul_of_nonneg_left eU.1 hε.le
  have b3 := mul_le_mul_of_nonneg_left eV.2 hε.le
  have b4 := mul_le_mul_of_nonneg_left eV.1 hε.le
  have r1 : (1 + ε) * (p * A + (1 - p) * V - W) = A + ε * V - (1 + ε) * W := by
    linear_combination A * hp + V * hq
  have r2 : (1 + ε) * (p * B + (1 - p) * U - W) = B + ε * U - (1 + ε) * W := by
    linear_combination B * hp + U * hq
  rw [r1] at a1 a2; rw [r2] at a3 a4
  have hc2 : ε * c ≤ c := by nlinarith
  rw [abs_le]; constructor <;> nlinarith

noncomputable section

open QAlgorithms QAlgorithms.Papers QAlgorithms.Papers.Independent QAlgorithms.Papers.Independent.Frontier30 QAlgorithms.Papers.Independent.Frontier30.P30

open scoped Matrix ComplexConjugate

open Filter

open QAlgorithms

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P21 (Op)

open QAlgorithms.Papers.Independent.Information100.P80 (log2)

theorem solution (f : Functional) (c M : ℝ)
    (hc : 0 ≤ c) (hM : 0 ≤ M) (haff : ApproximateAffinity f c) (hsub : Subextensive f M) :
    ∀ d : ℕ, 0 < d → ∀ rho sigma : Op (Fin d),
      IsDensityMatrix rho → IsDensityMatrix sigma →
      |f d rho-f d sigma| ≤ M * traceNorm (rho-sigma) * log2 d + 4*c := by
  intro d hd rho sigma hrho hsigma
  have hX : (rho - sigma).IsHermitian := hrho.1.isHermitian.sub hsigma.1.isHermitian
  have hparts := g53_parts (rho - sigma) hX
  have hPp := g53_cfc_psd (rho - sigma) (fun t : ℝ => max t 0) (fun t => le_max_right _ _)
  have hPm := g53_cfc_psd (rho - sigma) (fun t : ℝ => max (-t) 0) (fun t => le_max_right _ _)
  have hle := g53_posPart_le hX hrho.1 hsigma.1 rfl
  rw [g53_traceNorm_herm hX]
  generalize cfc (fun t : ℝ => max t 0) (rho - sigma) = Xp at *
  generalize cfc (fun t : ℝ => max (-t) 0) (rho - sigma) = Xm at *
  have hlog : 0 ≤ log2 (d : ℝ) := by
    unfold log2
    apply div_nonneg (Real.log_nonneg (by exact_mod_cast hd)) (Real.log_nonneg (by norm_num))
  have htrX : Xp.trace = Xm.trace := by
    have := congrArg Matrix.trace hparts
    rw [Matrix.trace_sub, Matrix.trace_sub, hrho.2, hsigma.2, sub_self] at this
    exact sub_eq_zero.mp this
  have hreal : ∀ Y : Op (Fin d), Y.PosSemidef → Y.trace = ((Y.trace.re : ℝ) : ℂ) := by
    intro Y hY
    have h0 := hY.trace_nonneg
    apply Complex.ext <;> simp [(Complex.nonneg_iff.mp h0).2.symm]
  set ε := Xp.trace.re with hεdef
  have hεm : Xm.trace.re = ε := by rw [← htrX]
  rw [hεm]
  have hε0 : 0 ≤ ε := (Complex.nonneg_iff.mp hPp.trace_nonneg).1
  have hε1 : ε ≤ 1 := by rw [hrho.2] at hle; simpa using hle
  rcases hε0.eq_or_lt with h0 | hεpos
  · -- ε = 0: rho = sigma
    have hp0 : Xp = 0 := by
      rw [← hPp.trace_eq_zero_iff, hreal Xp hPp, ← hεdef, ← h0]; simp
    have hm0 : Xm = 0 := by
      rw [← hPm.trace_eq_zero_iff, hreal Xm hPm, hεm, ← h0]; simp
    rw [hp0, hm0, sub_zero] at hparts
    rw [sub_eq_zero.mp hparts.symm, sub_self, abs_zero]
    rw [← h0]; nlinarith
  · set Dp : Op (Fin d) := ((ε⁻¹ : ℝ) : ℂ) • Xp with hDp
    set Dm : Op (Fin d) := ((ε⁻¹ : ℝ) : ℂ) • Xm with hDm
    have hinv : (0 : ℂ) ≤ ((ε⁻¹ : ℝ) : ℂ) := by
      exact_mod_cast (inv_nonneg.mpr hε0)
    have hdens : ∀ Y : Op (Fin d), Y.PosSemidef → Y.trace.re = ε →
        IsDensityMatrix (((ε⁻¹ : ℝ) : ℂ) • Y) := by
      intro Y hY hYt
      refine ⟨hY.smul hinv, ?_⟩
      rw [Matrix.trace_smul, hreal Y hY, hYt, smul_eq_mul, ← Complex.ofReal_mul,
        inv_mul_cancel₀ hεpos.ne']
      simp
    have hDpd : IsDensityMatrix Dp := hdens Xp hPp rfl
    have hDmd : IsDensityMatrix Dm := hdens Xm hPm hεm
    set p : ℝ := (1 + ε)⁻¹ with hpdef
    have hp : p * (1 + ε) = 1 := inv_mul_cancel₀ (by linarith)
    have hp0 : 0 ≤ p := inv_nonneg.mpr (by linarith)
    have hp1 : p ≤ 1 := inv_le_one_of_one_le₀ (by linarith)
    have hq : ((1 - p : ℝ) : ℂ) * ((ε⁻¹ : ℝ) : ℂ) = (p : ℂ) := by
      rw [← Complex.ofReal_mul]; congr 1
      field_simp
      linarith
    have hmix : densityMix p rho Dm = densityMix p sigma Dp := by
      unfold densityMix
      rw [hDp, hDm, smul_smul, smul_smul, hq, ← smul_add, ← smul_add]
      congr 1
      have : rho = sigma + (Xp - Xm) := by rw [hparts]; abel
      rw [this]; abel
    have h1 := haff d hd rho Dm hrho hDmd p hp0 hp1
    have h2 := haff d hd sigma Dp hsigma hDpd p hp0 hp1
    rw [hmix] at h1
    have hU := hsub d hd Dp hDpd
    have hV := hsub d hd Dm hDmd
    have := g53_real_aff (f d rho) (f d sigma) (f d Dp) (f d Dm) (f d (densityMix p sigma Dp))
      c M (log2 d) ε p hεpos hε1 hp hc h1 h2 hU hV
    linarith
