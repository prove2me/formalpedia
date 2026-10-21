-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Information100.P08.dampingMaximumOutput
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-20T09:46:47.920769+00:00
-- url     : https://prove2.me/submissions/004931e1-c7bd-4b3b-aeff-0b6456a6bc95

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P08

open QAlgorithms.Papers.Independent.Information100.P08

open scoped Matrix ComplexConjugate ComplexOrder

noncomputable section

attribute [local instance] Classical.propDecidable

namespace G56DM

open QAlgorithms.Papers.Independent.Independent2.P01 (damping dampingKraus) in
lemma fd (g : ℝ) (ρ : Matrix (Fin 2) (Fin 2) ℂ) (i j : Fin 2) :
    finDamping g ρ i j = QAlgorithms.krausApply (dampingKraus g)
      (Matrix.of fun b c => ρ (cond b 1 0) (cond c 1 0)) (i.val == 1) (j.val == 1) := rfl

lemma fd00 (g : ℝ) (hg0 : 0 ≤ g) (hg1 : g ≤ 1) (ρ : Matrix (Fin 2) (Fin 2) ℂ) :
    finDamping g ρ 0 0 = ρ 0 0 + (g : ℂ) * ρ 1 1 := by
  have h2 : (Real.sqrt g : ℂ) * (Real.sqrt g : ℂ) = (g : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt hg0]
  rw [fd]
  simp only [QAlgorithms.Papers.Independent.Independent2.P01.dampingKraus, QAlgorithms.krausApply, Fintype.sum_bool, Matrix.add_apply, Matrix.mul_apply, Matrix.of_apply, Matrix.conjTranspose_apply]
  simp [
    Matrix.mul_apply, Fintype.sum_bool, Matrix.diagonal_apply, Complex.conj_ofReal]
  linear_combination (ρ 1 1) * h2

lemma fd11 (g : ℝ) (hg0 : 0 ≤ g) (hg1 : g ≤ 1) (ρ : Matrix (Fin 2) (Fin 2) ℂ) :
    finDamping g ρ 1 1 = (1 - (g : ℂ)) * ρ 1 1 := by
  have h1 : (Real.sqrt (1 - g) : ℂ) * (Real.sqrt (1 - g) : ℂ) = 1 - (g : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by linarith)]; push_cast; ring
  rw [fd]
  simp only [QAlgorithms.Papers.Independent.Independent2.P01.dampingKraus, QAlgorithms.krausApply, Fintype.sum_bool, Matrix.add_apply, Matrix.mul_apply, Matrix.of_apply, Matrix.conjTranspose_apply]
  simp [
    Matrix.mul_apply, Fintype.sum_bool, Matrix.diagonal_apply, Complex.conj_ofReal]
  linear_combination (ρ 1 1) * h1

lemma fd01 (g : ℝ) (hg0 : 0 ≤ g) (hg1 : g ≤ 1) (ρ : Matrix (Fin 2) (Fin 2) ℂ) :
    finDamping g ρ 0 1 = (Real.sqrt (1 - g) : ℂ) * ρ 0 1 := by
  rw [fd]
  simp only [QAlgorithms.Papers.Independent.Independent2.P01.dampingKraus, QAlgorithms.krausApply, Fintype.sum_bool, Matrix.add_apply, Matrix.mul_apply, Matrix.of_apply, Matrix.conjTranspose_apply]
  simp [
    Matrix.mul_apply, Fintype.sum_bool, Matrix.diagonal_apply, Complex.conj_ofReal]
  ring

lemma fd10 (g : ℝ) (hg0 : 0 ≤ g) (hg1 : g ≤ 1) (ρ : Matrix (Fin 2) (Fin 2) ℂ) :
    finDamping g ρ 1 0 = (Real.sqrt (1 - g) : ℂ) * ρ 1 0 := by
  rw [fd]
  simp only [QAlgorithms.Papers.Independent.Independent2.P01.dampingKraus, QAlgorithms.krausApply, Fintype.sum_bool, Matrix.add_apply, Matrix.mul_apply, Matrix.of_apply, Matrix.conjTranspose_apply]
  simp [
    Matrix.mul_apply, Fintype.sum_bool, Matrix.diagonal_apply, Complex.conj_ofReal]

end G56DM

namespace G56DM

lemma cfc_trace {n : Type} [Fintype n] [DecidableEq n] {Y : Matrix n n ℂ} (hY : Y.IsHermitian)
    (f : ℝ → ℝ) : (cfc f Y).trace = ∑ i, ((f (hY.eigenvalues i) : ℝ) : ℂ) := by
  rw [hY.cfc_eq f, Matrix.IsHermitian.cfc, Unitary.conjStarAlgAut_apply, Matrix.trace_mul_cycle,
    Unitary.star_mul_self_of_mem hY.eigenvectorUnitary.2, one_mul, Matrix.trace_diagonal]
  rfl

lemma ent (σ : Matrix (Fin 2) (Fin 2) ℂ) (hσ : σ.IsHermitian) (htr : σ.trace = 1) :
    hσ.eigenvalues 1 = 1 - hσ.eigenvalues 0 ∧
    hσ.eigenvalues 0 * hσ.eigenvalues 1 = σ.det.re ∧
    QAlgorithms.vnEntropy σ = QAlgorithms.binEntropy2 (hσ.eigenvalues 0) := by
  have hs := hσ.trace_eq_sum_eigenvalues
  have hd := hσ.det_eq_prod_eigenvalues
  rw [Fin.sum_univ_two] at hs
  rw [Fin.prod_univ_two] at hd
  rw [htr] at hs
  have h1 : hσ.eigenvalues 1 = 1 - hσ.eigenvalues 0 := by
    have := congrArg Complex.re hs
    simp at this; linarith
  refine ⟨h1, ?_, ?_⟩
  · rw [hd]; simp
  · unfold QAlgorithms.vnEntropy QAlgorithms.binEntropy2
    rw [cfc_trace hσ, Fin.sum_univ_two, h1]
    simp only [Complex.add_re, Complex.ofReal_re, Real.binEntropy, Real.logb, Real.log_inv]
    field_simp
    ring

lemma cmp (l p : ℝ) (hl0 : 0 ≤ l) (hl1 : l ≤ 1) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (h : l * (1 - l) ≤ p * (1 - p)) : Real.binEntropy l ≤ Real.binEntropy p := by
  -- reduce to the half [0, 1/2]
  have key : ∀ x : ℝ, 0 ≤ x → x ≤ 1 → ∃ y, 0 ≤ y ∧ y ≤ 2⁻¹ ∧ Real.binEntropy y = Real.binEntropy x ∧
      y * (1 - y) = x * (1 - x) := by
    intro x hx0 hx1
    by_cases hx : x ≤ 2⁻¹
    · exact ⟨x, hx0, hx, rfl, rfl⟩
    · refine ⟨1 - x, by linarith, by linarith, Real.binEntropy_one_sub x, by ring⟩
  obtain ⟨l', hl'0, hl'1, hl'e, hl'm⟩ := key l hl0 hl1
  obtain ⟨p', hp'0, hp'1, hp'e, hp'm⟩ := key p hp0 hp1
  rw [← hl'e, ← hp'e]
  have hle : l' ≤ p' := by
    by_contra hc
    push Not at hc
    have : p' * (1 - p') < l' * (1 - l') := by nlinarith
    linarith
  exact Real.binEntropy_strictMonoOn.monotoneOn ⟨hl'0, hl'1⟩ ⟨hp'0, hp'1⟩ hle

end G56DM

namespace G56DM

lemma real_data (ρ : Matrix (Fin 2) (Fin 2) ℂ) (hρ : QAlgorithms.IsDensityMatrix ρ) :
    ρ 1 1 = (((ρ 1 1).re : ℝ) : ℂ) ∧ ρ 0 0 = ((1 - (ρ 1 1).re : ℝ) : ℂ) ∧ ρ 1 0 = starRingEnd ℂ (ρ 0 1) ∧
    Complex.normSq (ρ 0 1) ≤ (ρ 1 1).re * (1 - (ρ 1 1).re) ∧ 0 ≤ (ρ 1 1).re ∧ (ρ 1 1).re ≤ 1 := by
  have hH := hρ.1.1
  have h11 : ρ 1 1 = (((ρ 1 1).re : ℝ) : ℂ) := by
    have := hH.apply 1 1
    apply Complex.ext
    · simp
    · have h2 := congrArg Complex.im this
      simp at h2; simp; linarith
  have h00' : ρ 0 0 = (((ρ 0 0).re : ℝ) : ℂ) := by
    have := hH.apply 0 0
    apply Complex.ext
    · simp
    · have h2 := congrArg Complex.im this
      simp at h2; simp; linarith
  have htr := hρ.2
  rw [Matrix.trace_fin_two] at htr
  have hre : (ρ 0 0).re + (ρ 1 1).re = 1 := by
    have := congrArg Complex.re htr; simpa using this
  have h00 : ρ 0 0 = ((1 - (ρ 1 1).re : ℝ) : ℂ) := by
    rw [h00']; congr 1; linarith
  have h10 : ρ 1 0 = starRingEnd ℂ (ρ 0 1) := (hH.apply 1 0).symm
  have hd := hρ.1.det_nonneg
  rw [Matrix.det_fin_two, h10] at hd
  have hd' := (Complex.nonneg_iff.mp hd).1
  rw [Complex.sub_re, Complex.mul_conj, Complex.ofReal_re, h00, h11] at hd'
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero] at hd'
  have hd0 := hρ.1.diag_nonneg (i := 1)
  have hd1 := hρ.1.diag_nonneg (i := 0)
  have ha0 : 0 ≤ (ρ 1 1).re := (Complex.nonneg_iff.mp hd0).1
  have ha1 : 0 ≤ (ρ 0 0).re := (Complex.nonneg_iff.mp hd1).1
  exact ⟨h11, h00, h10, by nlinarith, ha0, by linarith⟩

lemma upper (g : ℝ) (hg0 : 0 ≤ g) (hg1 : g ≤ 1) (ρ : Matrix (Fin 2) (Fin 2) ℂ)
    (hρ : QAlgorithms.IsDensityMatrix ρ) :
    QAlgorithms.vnEntropy (finDamping g ρ) ≤ if g ≤ 1 / 2 then 1 else QAlgorithms.binEntropy2 (1 - g) := by
  obtain ⟨h11, h00, h10, hn, ha0, ha1⟩ := real_data ρ hρ
  set a := (ρ 1 1).re
  set r := ρ 0 1
  set σ := finDamping g ρ
  have s00 : σ 0 0 = ((1 - a + g * a : ℝ) : ℂ) := by
    simp only [σ]; rw [fd00 g hg0 hg1, h00, h11]; push_cast; ring
  have s11 : σ 1 1 = (((1 - g) * a : ℝ) : ℂ) := by
    simp only [σ]; rw [fd11 g hg0 hg1, h11]; push_cast; ring
  have s01 : σ 0 1 = (Real.sqrt (1 - g) : ℂ) * r := fd01 g hg0 hg1 ρ
  have s10 : σ 1 0 = (Real.sqrt (1 - g) : ℂ) * starRingEnd ℂ r := by
    simp only [σ]; rw [fd10 g hg0 hg1, h10]
  have hH : σ.IsHermitian := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.conjTranspose_apply, s00, s11, s01, s10, Complex.conj_ofReal]
  have htr : σ.trace = 1 := by
    rw [Matrix.trace_fin_two, s00, s11]; push_cast; ring
  have hdet : σ.det.re = (1 - a + g * a) * ((1 - g) * a) - (1 - g) * Complex.normSq r := by
    rw [Matrix.det_fin_two, s00, s11, s01, s10]
    have : (Real.sqrt (1 - g) : ℂ) * r * ((Real.sqrt (1 - g) : ℂ) * starRingEnd ℂ r) =
        (((1 - g) * Complex.normSq r : ℝ) : ℂ) := by
      rw [show (Real.sqrt (1 - g) : ℂ) * r * ((Real.sqrt (1 - g) : ℂ) * starRingEnd ℂ r) =
        ((Real.sqrt (1 - g) * Real.sqrt (1 - g) : ℝ) : ℂ) * (r * starRingEnd ℂ r) by push_cast; ring,
        Complex.mul_conj, Real.mul_self_sqrt (by linarith)]
      push_cast; ring
    rw [this, ← Complex.ofReal_mul, ← Complex.ofReal_sub, Complex.ofReal_re]
  obtain ⟨he1, hprod, hent⟩ := ent σ hH htr
  rw [hent]
  set e := hH.eigenvalues 0
  rw [he1, hdet] at hprod
  set p := (1 - g) * a
  have hp0 : 0 ≤ p := mul_nonneg (by linarith) ha0
  have hp1 : p ≤ 1 - g := by nlinarith
  have hn0 := Complex.normSq_nonneg r
  have hupper : e * (1 - e) ≤ p * (1 - p) := by
    have : p * (1 - p) - (1 - a + g * a) * ((1 - g) * a) = 0 := by ring
    nlinarith
  have hlow : 0 ≤ e * (1 - e) := by
    rw [hprod]; nlinarith [mul_nonneg hg0 (mul_nonneg ha0 ha0), mul_nonneg (show 0 ≤ 1 - g by linarith) hg0]
  have he0 : 0 ≤ e := by
    by_contra h; push Not at h; nlinarith
  have he1' : e ≤ 1 := by
    by_contra h; push Not at h; nlinarith
  have hc := cmp e p he0 he1' hp0 (by linarith) hupper
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  unfold QAlgorithms.binEntropy2
  split_ifs with hg
  · rw [div_le_one hlog]
    exact hc.trans Real.binEntropy_le_log_two
  · apply div_le_div_of_nonneg_right _ hlog.le
    refine hc.trans ?_
    exact Real.binEntropy_strictMonoOn.monotoneOn ⟨hp0, by linarith⟩ ⟨by linarith, by linarith⟩ hp1

end G56DM

namespace G56DM

def rt (t : ℝ) : Matrix (Fin 2) (Fin 2) ℂ := Matrix.diagonal fun i => if i = 0 then ((1 - t : ℝ) : ℂ) else (t : ℂ)

lemma rt_dens (t : ℝ) (h0 : 0 ≤ t) (h1 : t ≤ 1) : QAlgorithms.IsDensityMatrix (rt t) := by
  refine ⟨Matrix.posSemidef_diagonal_iff.mpr fun i => ?_, ?_⟩
  · split_ifs
    · exact_mod_cast (show (0:ℝ) ≤ 1 - t by linarith)
    · exact_mod_cast h0
  · simp [rt, Matrix.trace_diagonal, Fin.sum_univ_two]

lemma rt_val (g : ℝ) (hg0 : 0 ≤ g) (hg1 : g ≤ 1) (t : ℝ) (h0 : 0 ≤ t) (h1 : t ≤ 1) :
    QAlgorithms.vnEntropy (finDamping g (rt t)) = QAlgorithms.binEntropy2 ((1 - g) * t) := by
  set σ := finDamping g (rt t)
  have s00 : σ 0 0 = ((1 - t + g * t : ℝ) : ℂ) := by
    simp only [σ]; rw [fd00 g hg0 hg1]; simp [rt]
  have s11 : σ 1 1 = (((1 - g) * t : ℝ) : ℂ) := by
    simp only [σ]; rw [fd11 g hg0 hg1]; simp [rt]
  have s01 : σ 0 1 = 0 := by simp only [σ]; rw [fd01 g hg0 hg1]; simp [rt]
  have s10 : σ 1 0 = 0 := by simp only [σ]; rw [fd10 g hg0 hg1]; simp [rt]
  have hH : σ.IsHermitian := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.conjTranspose_apply, s00, s11, s01, s10, Complex.conj_ofReal]
  have htr : σ.trace = 1 := by
    rw [Matrix.trace_fin_two, s00, s11]; push_cast; ring
  obtain ⟨he1, hprod, hent⟩ := ent σ hH htr
  rw [hent]
  rw [he1, Matrix.det_fin_two, s00, s11, s01, s10] at hprod
  simp only [mul_zero, sub_zero, ← Complex.ofReal_mul, Complex.ofReal_re] at hprod
  set e := hH.eigenvalues 0
  set p := (1 - g) * t
  have hfac : (e - p) * (e - (1 - p)) = 0 := by nlinarith
  rcases mul_eq_zero.mp hfac with h | h
  · rw [show e = p by linarith]
  · rw [show e = 1 - p by linarith]
    unfold QAlgorithms.binEntropy2; rw [Real.binEntropy_one_sub]

end G56DM

open QAlgorithms

open G56DM in
theorem solution (g : ℝ) (hg : g ∈ Set.Icc (0 : ℝ) 1) :
    sSup {r | ∃ rho : Matrix (Fin 2) (Fin 2) ℂ,
      IsDensityMatrix rho ∧ r = vnEntropy (finDamping g rho)} =
      if g ≤ 1 / 2 then 1 else binEntropy2 (1 - g) := by
  obtain ⟨hg0, hg1⟩ := hg
  apply IsGreatest.csSup_eq
  refine ⟨?_, ?_⟩
  · split_ifs with h
    · have hpos : 0 < 1 - g := by linarith
      refine ⟨rt (1 / (2 * (1 - g))), rt_dens _ (by positivity) ?_, ?_⟩
      · rw [div_le_one (by positivity)]; linarith
      · rw [rt_val g hg0 hg1 _ (by positivity) (by rw [div_le_one (by positivity)]; linarith)]
        have : (1 - g) * (1 / (2 * (1 - g))) = 2⁻¹ := by field_simp
        rw [this]; unfold QAlgorithms.binEntropy2
        rw [Real.binEntropy_two_inv, div_self (Real.log_pos (by norm_num)).ne']
    · refine ⟨rt 1, rt_dens 1 zero_le_one le_rfl, ?_⟩
      rw [rt_val g hg0 hg1 1 zero_le_one le_rfl, mul_one]
  · rintro r ⟨rho, hrho, rfl⟩
    exact upper g hg0 hg1 rho hrho
