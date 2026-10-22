-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Claimed50.P12.lemmaA_5
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T09:55:42.887929+00:00
-- url     : https://prove2.me/submissions/fdc46597-bf71-486e-88d7-3a1807f72e2f

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P12
noncomputable section

open Filter MeasureTheory

open scoped Matrix ComplexConjugate ComplexOrder ENNReal

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms QAlgorithms.Papers QAlgorithms.Papers.Independent QAlgorithms.Papers.Independent.Claimed50
open QAlgorithms.Papers.Independent.Claimed50.P12
open scoped MatrixOrder

open QAlgorithms.Papers.Independent.Information100.P32 (Op)

open QAlgorithms.Papers.Independent.Information100.P69 (CP matrixPower permute)

open QAlgorithms.Papers.Independent.Information100.P80 (OperatorLE groupedPower)

open QAlgorithms.Papers.Independent.Dependency50.P21 (marginalAB)

open scoped Matrix ComplexOrder MatrixOrder InnerProductSpace

lemma g68m_x_parts {n : Type*} [Fintype n] [DecidableEq n] (X : Matrix n n ℂ) (hX : X.IsHermitian) :
    cfc (fun t : ℝ => max t 0) X - cfc (fun t : ℝ => max (-t) 0) X = X := by
  have hsa : IsSelfAdjoint X := hX.isSelfAdjoint
  rw [← cfc_sub (fun t : ℝ => max t 0) (fun t : ℝ => max (-t) 0) X]
  conv_rhs => rw [← cfc_id ℝ X]
  apply cfc_congr
  intro t _
  simp only [id]
  rcases le_total t 0 with h | h <;> simp [h]

lemma g68m_x_cfc_psd {n : Type*} [Fintype n] [DecidableEq n] (X : Matrix n n ℂ) (f : ℝ → ℝ)
    (hf : ∀ t, 0 ≤ f t) : (cfc f X).PosSemidef := by
  rw [← Matrix.nonneg_iff_posSemidef]
  exact cfc_nonneg (fun t _ => hf t)

lemma g68m_x_traceNorm_herm {n : Type*} [Fintype n] [DecidableEq n] {X : Matrix n n ℂ} (hX : X.IsHermitian) :
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



lemma g68m_sqrt_psd {n : Type*} [Fintype n] [DecidableEq n] (Y : Matrix n n ℂ) :
    (cfc Real.sqrt Y).PosSemidef := by
  rw [← Matrix.nonneg_iff_posSemidef]
  exact cfc_nonneg (fun t _ => Real.sqrt_nonneg t)

lemma g68m_sqrt_mul_sqrt {n : Type*} [Fintype n] [DecidableEq n] {Q : Matrix n n ℂ}
    (hQ : Q.PosSemidef) : cfc Real.sqrt Q * cfc Real.sqrt Q = Q := by
  have hnn : (0 : Matrix n n ℂ) ≤ Q := Matrix.nonneg_iff_posSemidef.mpr hQ
  rw [← cfc_mul Real.sqrt Real.sqrt Q]
  conv_rhs => rw [← cfc_id ℝ Q]
  apply cfc_congr
  intro t ht
  exact Real.mul_self_sqrt (spectrum_nonneg_of_nonneg hnn ht)

lemma g68m_tr_psd_mul {n : Type*} [Fintype n] [DecidableEq n] {P Q : Matrix n n ℂ}
    (hP : P.PosSemidef) (hQ : Q.PosSemidef) : 0 ≤ (P * Q).trace.re := by
  have hR : (cfc Real.sqrt Q)ᴴ = cfc Real.sqrt Q := (g68m_sqrt_psd Q).1.eq
  have h := (hP.conjTranspose_mul_mul_same (cfc Real.sqrt Q)).trace_nonneg
  rw [hR, Matrix.trace_mul_comm, ← Matrix.mul_assoc, g68m_sqrt_mul_sqrt hQ,
    Matrix.trace_mul_comm] at h
  exact (Complex.nonneg_iff.mp h).1

lemma g68m_effect_bound {n : Type*} [Fintype n] [DecidableEq n] (Q X : Matrix n n ℂ)
    (hQ : IsEffect Q) (hX : X.IsHermitian) :
    (Q * X).trace.re ≤ (QAlgorithms.traceNorm X + X.trace.re) / 2 := by
  set Xp := cfc (fun t : ℝ => max t 0) X
  set Xm := cfc (fun t : ℝ => max (-t) 0) X
  have hp : Xp.PosSemidef := g68m_x_cfc_psd X _ (fun t => le_max_right _ _)
  have hm : Xm.PosSemidef := g68m_x_cfc_psd X _ (fun t => le_max_right _ _)
  have hparts : Xp - Xm = X := g68m_x_parts X hX
  have htn := g68m_x_traceNorm_herm hX
  have h1 : 0 ≤ ((1 - Q) * Xp).trace.re := g68m_tr_psd_mul hQ.2 hp
  have h2 : 0 ≤ (Q * Xm).trace.re := g68m_tr_psd_mul hQ.1 hm
  have htr : X.trace.re = Xp.trace.re - Xm.trace.re := by
    rw [← hparts, Matrix.trace_sub, Complex.sub_re]
  have hQX : (Q * X).trace.re = (Q * Xp).trace.re - (Q * Xm).trace.re := by
    rw [← hparts, Matrix.mul_sub, Matrix.trace_sub, Complex.sub_re]
  have h1' : ((1 - Q) * Xp).trace.re = Xp.trace.re - (Q * Xp).trace.re := by
    rw [Matrix.sub_mul, Matrix.one_mul, Matrix.trace_sub, Complex.sub_re]
  rw [htn]
  linarith

theorem solution {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I]
    (rho bar sigma : Op I) (hrho : rho.PosSemidef) (hbar : bar.PosSemidef)
    (hsigma : sigma.PosSemidef) (lam epsilon : ℝ) (hlam : 0 < lam)
    (hbound : OperatorLE bar ((lam : ℂ) • sigma)) (hepsilon : 0 < epsilon)
    (htrace : epsilon ≤ rho.trace.re) (hdistance : generalizedTraceDistance rho bar < epsilon) :
    normalizedTestingEntropyBits epsilon rho sigma ≤
      ((Real.logb 2 lam - Real.logb 2 (1-generalizedTraceDistance rho bar/epsilon) : ℝ) : EReal) := by
  set Δ := generalizedTraceDistance rho bar with hΔ
  have hX : (rho - bar).IsHermitian := hrho.isHermitian.sub hbar.isHermitian
  have claim : ∀ Q : Op I, IsEffect Q → epsilon ≤ (Q * rho).trace.re →
      (epsilon - Δ) / lam ≤ (Q * sigma).trace.re := by
    intro Q hQ hfeas
    have hb := g68m_effect_bound Q (rho - bar) hQ hX
    have hD : (QAlgorithms.traceNorm (rho - bar) + (rho - bar).trace.re) / 2 ≤ Δ := by
      rw [hΔ, generalizedTraceDistance, QAlgorithms.traceDistance]
      have := le_abs_self (rho - bar).trace.re
      linarith
    have hs : 0 ≤ (Q * ((lam : ℂ) • sigma - bar)).trace.re := g68m_tr_psd_mul hQ.1 hbound
    rw [Matrix.mul_sub, Matrix.trace_sub, Complex.sub_re, Matrix.mul_smul, Matrix.trace_smul,
      smul_eq_mul, Complex.re_ofReal_mul] at hs
    rw [Matrix.mul_sub, Matrix.trace_sub, Complex.sub_re] at hb
    rw [div_le_iff₀ hlam]
    linarith
  set m : ℝ := (epsilon - Δ) / (lam * epsilon)
  have hm : 0 < m := div_pos (by linarith) (mul_pos hlam hepsilon)
  have hle : ENNReal.ofReal m ≤ sInf {v : ℝ≥0∞ | ∃ Q : Op I, IsEffect Q ∧
      epsilon ≤ (Q*rho).trace.re ∧ v = ENNReal.ofReal ((Q*sigma).trace.re / epsilon)} := by
    apply le_sInf
    rintro v ⟨Q, hQ, hfeas, rfl⟩
    apply ENNReal.ofReal_le_ofReal
    have := claim Q hQ hfeas
    rw [show m = (epsilon - Δ) / lam / epsilon by rw [div_div]]
    exact div_le_div_of_nonneg_right this hepsilon.le
  unfold normalizedTestingEntropyBits negLogBits
  set s := sInf {v : ℝ≥0∞ | ∃ Q : Op I, IsEffect Q ∧
      epsilon ≤ (Q*rho).trace.re ∧ v = ENNReal.ofReal ((Q*sigma).trace.re / epsilon)}
  have hs0 : s ≠ 0 := by
    intro h; rw [h] at hle; simp at hle; linarith
  rw [if_neg hs0]
  split_ifs with hst
  · exact bot_le
  · have hsr : m ≤ s.toReal := by
      have := ENNReal.toReal_mono hst hle
      rwa [ENNReal.toReal_ofReal hm.le] at this
    have hkey : Real.logb 2 lam - Real.logb 2 (1 - Δ / epsilon) = -Real.logb 2 m := by
      have h1 : 0 < 1 - Δ / epsilon := by
        rw [sub_pos, div_lt_one hepsilon]; exact hdistance
      have : m = (1 - Δ / epsilon) / lam := by
        simp only [m]; field_simp
      rw [this, Real.logb_div h1.ne' hlam.ne']; ring
    rw [hkey, EReal.coe_le_coe_iff, neg_le_neg_iff]
    exact Real.logb_le_logb_of_le (by norm_num) hm hsr

end
