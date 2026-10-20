-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Frontier30.P30.convex_monotone_locking
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-20T03:14:01.817076+00:00
-- url     : https://prove2.me/submissions/179ee669-dd89-43dd-a5b9-937a02d1631e

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

open Filter Topology

open QAlgorithms

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P21 (Op)

open QAlgorithms.Papers.Independent.Information100.P80 (log2)

theorem g53_aac_gen {ι : Type} [Fintype ι] [DecidableEq ι] (f : Op ι → ℝ) (c M L : ℝ)
    (hc : 0 ≤ c) (hML : 0 ≤ M * L)
    (haff : ∀ rho sigma : Op ι, IsDensityMatrix rho → IsDensityMatrix sigma → ∀ p : ℝ, 0 ≤ p → p ≤ 1 →
      |p * f rho + (1 - p) * f sigma - f (densityMix p rho sigma)| ≤ c)
    (hsub : ∀ rho : Op ι, IsDensityMatrix rho → |f rho| ≤ M * L) :
    ∀ rho sigma : Op ι, IsDensityMatrix rho → IsDensityMatrix sigma →
      |f rho - f sigma| ≤ M * traceNorm (rho - sigma) * L + 4 * c := by
  intro rho sigma hrho hsigma
  have hX : (rho - sigma).IsHermitian := hrho.1.isHermitian.sub hsigma.1.isHermitian
  have hparts := g53_parts (rho - sigma) hX
  have hPp := g53_cfc_psd (rho - sigma) (fun t : ℝ => max t 0) (fun t => le_max_right _ _)
  have hPm := g53_cfc_psd (rho - sigma) (fun t : ℝ => max (-t) 0) (fun t => le_max_right _ _)
  have hle := g53_posPart_le hX hrho.1 hsigma.1 rfl
  rw [g53_traceNorm_herm hX]
  generalize cfc (fun t : ℝ => max t 0) (rho - sigma) = Xp at *
  generalize cfc (fun t : ℝ => max (-t) 0) (rho - sigma) = Xm at *
  have htrX : Xp.trace = Xm.trace := by
    have := congrArg Matrix.trace hparts
    rw [Matrix.trace_sub, Matrix.trace_sub, hrho.2, hsigma.2, sub_self] at this
    exact sub_eq_zero.mp this
  have hreal : ∀ Y : Op ι, Y.PosSemidef → Y.trace = ((Y.trace.re : ℝ) : ℂ) := by
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
  · set Dp : Op ι := ((ε⁻¹ : ℝ) : ℂ) • Xp with hDp
    set Dm : Op ι := ((ε⁻¹ : ℝ) : ℂ) • Xm with hDm
    have hinv : (0 : ℂ) ≤ ((ε⁻¹ : ℝ) : ℂ) := by
      exact_mod_cast (inv_nonneg.mpr hε0)
    have hdens : ∀ Y : Op ι, Y.PosSemidef → Y.trace.re = ε →
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
    have h1 := haff rho Dm hrho hDmd p hp0 hp1
    have h2 := haff sigma Dp hsigma hDpd p hp0 hp1
    rw [hmix] at h1
    have hU := hsub Dp hDpd
    have hV := hsub Dm hDmd
    have := g53_real_aff (f rho) (f sigma) (f Dp) (f Dm) (f (densityMix p sigma Dp))
      c M L ε p hεpos hε1 hp hc h1 h2 hU hV
    linarith

namespace G53Lock


noncomputable def K (a : ℕ) (q : Fin 2) : Matrix (Fin a) (Fin (2 * a)) ℂ :=
  fun j x => if (flagEquiv a).symm x = (q, j) then 1 else 0

lemma K_apply (a : ℕ) (q : Fin 2) (j : Fin a) (x : Fin (2 * a)) :
    K a q j x = if (flagEquiv a).symm x = (q, j) then 1 else 0 := rfl

lemma sum_flag {a : ℕ} (g : Fin (2 * a) → ℂ) : ∑ x, g x = ∑ q : Fin 2, ∑ j : Fin a, g (flagEquiv a (q, j)) := by
  rw [← (flagEquiv a).sum_comp, Fintype.sum_prod_type]

lemma lift_apply {a b : ℕ} (q : Fin 2) (Y : Op (Fin a × Fin b)) (u v : Fin 2 × Fin a) (s s' : Fin b) :
    ((Matrix.kronecker (K a q) (1 : Matrix (Fin b) (Fin b) ℂ))ᴴ * Y *
      Matrix.kronecker (K a q) (1 : Matrix (Fin b) (Fin b) ℂ)) (flagEquiv a u, s) (flagEquiv a v, s') =
      if u.1 = q ∧ v.1 = q then Y (u.2, s) (v.2, s') else 0 := by
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.kronecker, Matrix.kroneckerMap_apply,
    Fintype.sum_prod_type, K_apply, Matrix.one_apply, Equiv.symm_apply_apply]
  obtain ⟨qu, ju⟩ := u
  obtain ⟨qv, jv⟩ := v
  simp only [Prod.mk.injEq]
  by_cases hu : qu = q <;> by_cases hv : qv = q <;>
    simp [hu, hv, Finset.sum_ite_eq, Finset.sum_ite_eq', mul_ite, ite_mul, apply_ite (starRingEnd ℂ)]
lemma branch_apply {a b : ℕ} (q : Fin 2) (Y : Op (Fin (2 * a) × Fin b)) (j j' : Fin a) (s s' : Fin b) :
    (Matrix.kronecker (K a q) (1 : Matrix (Fin b) (Fin b) ℂ) * Y *
      (Matrix.kronecker (K a q) (1 : Matrix (Fin b) (Fin b) ℂ))ᴴ) (j, s) (j', s') =
      Y (flagEquiv a (q, j), s) (flagEquiv a (q, j'), s') := by
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.kronecker, Matrix.kroneckerMap_apply,
    Fintype.sum_prod_type, K_apply, Matrix.one_apply]
  rw [sum_flag]
  simp_rw [sum_flag (a := a)]
  simp [Equiv.symm_apply_apply, Prod.mk.injEq, Finset.sum_ite_eq, Finset.sum_ite_eq', mul_ite, ite_mul,
    apply_ite (starRingEnd ℂ), ite_and]

lemma kraus (a : ℕ) : QAlgorithms.IsKrausFamily (K a) := by
  unfold QAlgorithms.IsKrausFamily
  ext x y
  obtain ⟨u, rfl⟩ := (flagEquiv a).surjective x
  obtain ⟨v, rfl⟩ := (flagEquiv a).surjective y
  simp only [Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, K_apply, Equiv.symm_apply_apply,
    Matrix.one_apply, (flagEquiv a).injective.eq_iff]
  obtain ⟨qu, ju⟩ := u
  obtain ⟨qv, jv⟩ := v
  simp [Prod.mk.injEq, Finset.sum_ite_eq, Finset.sum_ite_eq', mul_ite, ite_mul, apply_ite (starRingEnd ℂ), ite_and]

noncomputable def lift {a b : ℕ} (q : Fin 2) (Y : Op (Fin a × Fin b)) : Op (Fin (2 * a) × Fin b) :=
  (Matrix.kronecker (K a q) (1 : Matrix (Fin b) (Fin b) ℂ))ᴴ * Y *
      Matrix.kronecker (K a q) (1 : Matrix (Fin b) (Fin b) ℂ)

lemma flagged_eq {a b : ℕ} (p : ℝ) (rho sigma : Op (Fin a × Fin b)) :
    flagged p rho sigma = lift 0 ((p : ℂ) • rho) + lift 1 (((1 - p : ℝ) : ℂ) • sigma) := by
  ext ⟨x, s⟩ ⟨y, s'⟩
  obtain ⟨⟨qu, ju⟩, rfl⟩ := (flagEquiv a).surjective x
  obtain ⟨⟨qv, jv⟩, rfl⟩ := (flagEquiv a).surjective y
  rw [Matrix.add_apply, lift, lift, lift_apply, lift_apply]
  simp only [flagged, Equiv.symm_apply_apply]
  fin_cases qu <;> fin_cases qv <;> simp

lemma erase_flagged {a b : ℕ} (p : ℝ) (rho sigma : Op (Fin a × Fin b)) :
    eraseDimensionedFlag (flagged p rho sigma) = densityMix p rho sigma := by
  ext x y
  simp only [eraseDimensionedFlag, flagged, Equiv.symm_apply_apply, densityMix, Fin.sum_univ_two,
    Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  simp

lemma branch_flagged {a b : ℕ} (p : ℝ) (rho sigma : Op (Fin a × Fin b)) (q : Fin 2) :
    Matrix.kronecker (K a q) (1 : Matrix (Fin b) (Fin b) ℂ) * flagged p rho sigma *
      (Matrix.kronecker (K a q) (1 : Matrix (Fin b) (Fin b) ℂ))ᴴ =
      if q = 0 then (p : ℂ) • rho else ((1 - p : ℝ) : ℂ) • sigma := by
  ext ⟨j, s⟩ ⟨j', s'⟩
  rw [branch_apply]
  simp only [flagged, Equiv.symm_apply_apply]
  fin_cases q <;> simp

lemma flagged_density {a b : ℕ} (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (rho sigma : Op (Fin a × Fin b))
    (hr : IsDensityMatrix rho) (hs : IsDensityMatrix sigma) : IsDensityMatrix (flagged p rho sigma) := by
  have h1 : (0 : ℂ) ≤ (p : ℂ) := by exact_mod_cast hp0
  have h2 : (0 : ℂ) ≤ ((1 - p : ℝ) : ℂ) := by exact_mod_cast (by linarith : (0:ℝ) ≤ 1 - p)
  refine ⟨?_, ?_⟩
  · rw [flagged_eq]
    exact ((hr.1.smul h1).conjTranspose_mul_mul_same _).add ((hs.1.smul h2).conjTranspose_mul_mul_same _)
  · have := congrArg Matrix.trace (erase_flagged p rho sigma)
    have e : (eraseDimensionedFlag (flagged p rho sigma)).trace = (flagged p rho sigma).trace := by
      simp only [Matrix.trace, Matrix.diag, eraseDimensionedFlag]
      rw [Fintype.sum_prod_type, Fintype.sum_prod_type, sum_flag]
      conv_lhs => enter [2, x]; rw [Finset.sum_comm]
      rw [Finset.sum_comm]
    rw [← e, this, densityMix, Matrix.trace_add, Matrix.trace_smul, Matrix.trace_smul, hr.2, hs.2]
    simp

end G53Lock

lemma g53_mean_smul (E : EntanglementFunctional) {a b : ℕ} (rho : Op (Fin a × Fin b))
    (hr : IsDensityMatrix rho) (w : ℝ) (hw : 0 ≤ w) :
    instrumentBranchMean E ((w : ℂ) • rho) = w * E a b rho := by
  unfold instrumentBranchMean
  have htr : ((w : ℂ) • rho).trace.re = w := by
    rw [Matrix.trace_smul, hr.2, smul_eq_mul, mul_one, Complex.ofReal_re]
  simp only [htr]
  rcases hw.eq_or_lt with h0 | hpos
  · rw [if_neg (by rw [← h0]; exact lt_irrefl 0), ← h0, zero_mul]
  · rw [if_pos hpos, smul_smul, ← Complex.ofReal_mul, inv_mul_cancel₀ hpos.ne', Complex.ofReal_one, one_smul]

theorem solution (E : EntanglementFunctional) (M : ℝ) (hM : 0 ≤ M)
    (hmono : IsLOCCMonotone E) (hconv : IsConvex E)
    (hsub : EntanglementSubextensive E M) (hfailure : EntanglementNoncontinuous E) :
    AdmitsLocking E := by
  intro loss
  by_contra hcon
  push Not at hcon
  have hmean : ∀ a b : ℕ, 0 < a → 0 < b → ∀ rho sigma : Op (Fin a × Fin b),
      IsDensityMatrix rho → IsDensityMatrix sigma → ∀ p : ℝ, 0 ≤ p → p ≤ 1 →
      p * E a b rho + (1 - p) * E a b sigma ≤ E (2 * a) b (flagged p rho sigma) := by
    intro a b ha hb rho sigma hr hs p hp0 hp1
    have := hmono.2.1 (2 * a) b a 2 (by omega) hb ha (G53Lock.K a) (G53Lock.kraus a) (flagged p rho sigma)
      (G53Lock.flagged_density p hp0 hp1 rho sigma hr hs)
    rw [Fin.sum_univ_two, G53Lock.branch_flagged, G53Lock.branch_flagged, if_pos rfl,
      if_neg (by decide), g53_mean_smul E rho hr p hp0, g53_mean_smul E sigma hs (1 - p) (by linarith)] at this
    exact this
  have haff : ∀ a b : ℕ, 0 < a → 0 < b → ∀ rho sigma : Op (Fin a × Fin b),
      IsDensityMatrix rho → IsDensityMatrix sigma → ∀ p : ℝ, 0 ≤ p → p ≤ 1 →
      |p * E a b rho + (1 - p) * E a b sigma - E a b (densityMix p rho sigma)| ≤ loss := by
    intro a b ha hb rho sigma hr hs p hp0 hp1
    have h1 := hmean a b ha hb rho sigma hr hs p hp0 hp1
    have h2 := hconv a b ha hb rho sigma hr hs p hp0 hp1
    have h3 := hcon a b ha hb rho sigma hr hs p hp0 hp1 (G53Lock.flagged_density p hp0 hp1 rho sigma hr hs)
    rw [G53Lock.erase_flagged] at h3
    rw [abs_le]; constructor <;> linarith
  obtain ⟨a, b, rho, sigma, gap, hgap, hds, hab, htn, hgapn⟩ := hfailure
  have hloss : 0 ≤ loss := le_trans (abs_nonneg _)
    (haff (a 0) (b 0) (hds 0).1 (hds 0).2.1 (rho 0) (sigma 0) (hds 0).2.2.2.1 (hds 0).2.2.2.2 0 le_rfl zero_le_one)
  have hL0 : ∀ n, 0 ≤ log2 ((a n : ℝ) * b n) := by
    intro n
    unfold log2
    apply div_nonneg _ (Real.log_nonneg (by norm_num))
    apply Real.log_nonneg
    have : (2 : ℝ) ≤ (a n : ℝ) * b n := by exact_mod_cast (hds n).2.2.1
    linarith
  have hmain : ∀ n, |E (a n) (b n) (rho n) - E (a n) (b n) (sigma n)| ≤
      M * traceNorm (rho n - sigma n) * log2 ((a n : ℝ) * b n) + 4 * loss := by
    intro n
    refine g53_aac_gen (E (a n) (b n)) loss M (log2 ((a n : ℝ) * b n)) hloss (mul_nonneg hM (hL0 n))
      (haff (a n) (b n) (hds n).1 (hds n).2.1) (fun D hD => ?_) (rho n) (sigma n)
      (hds n).2.2.2.1 (hds n).2.2.2.2
    have e1 := hmono.1 (a n) (b n) (hds n).1 (hds n).2.1 D hD
    have e2 := hsub (a n) (b n) (hds n).1 (hds n).2.1 D hD
    rw [abs_le]; constructor <;> nlinarith [mul_nonneg hM (hL0 n)]
  have hlog : Tendsto (fun n => log2 ((a n : ℝ) * b n)) atTop atTop := by
    unfold log2
    exact (Real.tendsto_log_atTop.comp hab).atTop_div_const (Real.log_pos (by norm_num))
  have hT : ∀ᶠ n in atTop, M * traceNorm (rho n - sigma n) ≤ gap / 2 := by
    have : Tendsto (fun n => M * traceNorm (rho n - sigma n)) atTop (𝓝 (M * 0)) := htn.const_mul M
    rw [mul_zero] at this
    exact this.eventually (ge_mem_nhds (by linarith))
  have hL := hlog.eventually_gt_atTop (8 * loss / gap)
  obtain ⟨n, hn1, hn2⟩ := (hT.and hL).exists
  have h1 := hmain n
  have h2 := hgapn n
  have hLpos : 0 < log2 ((a n : ℝ) * b n) := lt_of_le_of_lt (div_nonneg (by linarith) hgap.le) hn2
  have h3 : M * traceNorm (rho n - sigma n) * log2 ((a n : ℝ) * b n) ≤ gap / 2 * log2 ((a n : ℝ) * b n) :=
    mul_le_mul_of_nonneg_right hn1 hLpos.le
  have h4 : gap * log2 ((a n : ℝ) * b n) ≤ gap / 2 * log2 ((a n : ℝ) * b n) + 4 * loss := by linarith
  have h5 : log2 ((a n : ℝ) * b n) ≤ 8 * loss / gap := by
    rw [le_div_iff₀ hgap]; nlinarith
  linarith
