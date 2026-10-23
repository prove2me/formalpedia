-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Information100.P41.jc_visibility_gap
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T13:42:36.311998+00:00
-- url     : https://prove2.me/submissions/488f8ac2-256f-491f-b4a8-adcbaaf75f2d

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P41

noncomputable section

open Real Set

namespace X6P41

def Phi (u : ℝ) : ℝ := (1 + u) * Real.log (1 + u) + (1 - u) * Real.log (1 - u)

lemma hd_log1 (x : ℝ) (h : -1 < x) :
    HasDerivAt (fun u : ℝ => Real.log (1 + u)) (1 / (1 + x)) x := by
  have a : HasDerivAt (fun u : ℝ => 1 + u) 1 x := (hasDerivAt_id x).const_add 1
  exact a.log (by linarith)

lemma hd_log2 (x : ℝ) (h : x < 1) :
    HasDerivAt (fun u : ℝ => Real.log (1 - u)) (-1 / (1 - x)) x := by
  have b : HasDerivAt (fun u : ℝ => 1 - u) (-1) x := by
    simpa using (hasDerivAt_id x).const_sub 1
  exact b.log (by linarith)

lemma hasDerivAt_Phi (u : ℝ) (h1 : -1 < u) (h2 : u < 1) :
    HasDerivAt Phi (Real.log (1 + u) - Real.log (1 - u)) u := by
  have a : HasDerivAt (fun u : ℝ => 1 + u) 1 u := (hasDerivAt_id u).const_add 1
  have b : HasDerivAt (fun u : ℝ => 1 - u) (-1) u := by
    simpa using (hasDerivAt_id u).const_sub 1
  have := (a.mul (hd_log1 u h1)).add (b.mul (hd_log2 u h2))
  have h1' : 1 + u ≠ 0 := by linarith
  have h2' : 1 - u ≠ 0 := by linarith
  have e : 1 * Real.log (1 + u) + (1 + u) * (1 / (1 + u)) +
      (-1 * Real.log (1 - u) + (1 - u) * (-1 / (1 - u))) = Real.log (1 + u) - Real.log (1 - u) := by
    field_simp; ring
  exact (this : HasDerivAt Phi _ u).congr_deriv e

lemma ca_log1 (x : ℝ) (h : -1 < x) : ContinuousAt (fun u : ℝ => Real.log (1 + u)) x :=
  (hd_log1 x h).continuousAt
lemma ca_log2 (x : ℝ) (h : x < 1) : ContinuousAt (fun u : ℝ => Real.log (1 - u)) x :=
  (hd_log2 x h).continuousAt

/-- k(u) = 2u/(1-u²) - (log(1+u) - log(1-u)) ≥ 0 on [0,1) -/
lemma k_nonneg (u : ℝ) (h0 : 0 ≤ u) (h1 : u < 1) :
    Real.log (1 + u) - Real.log (1 - u) ≤ 2 * u / (1 - u ^ 2) := by
  let k : ℝ → ℝ := fun u => 2 * u / (1 - u ^ 2) - (Real.log (1 + u) - Real.log (1 - u))
  have hd : ∀ x ∈ Ioo (0:ℝ) 1, HasDerivAt k (4 * x ^ 2 / (1 - x ^ 2) ^ 2) x := by
    intro x ⟨hx0, hx1⟩
    have hne : 1 - x ^ 2 ≠ 0 := by nlinarith
    have n1 : HasDerivAt (fun u : ℝ => 2 * u) 2 x := by
      simpa using (hasDerivAt_id x).const_mul 2
    have d1 : HasDerivAt (fun u : ℝ => 1 - u ^ 2) (-(2 * x)) x := by
      simpa using ((hasDerivAt_pow 2 x).const_sub 1)
    have := (n1.div d1 hne).sub ((hd_log1 x (by linarith)).sub (hd_log2 x hx1))
    have h1' : 1 + x ≠ 0 := by linarith
    have h2' : 1 - x ≠ 0 := by linarith
    have e : (2 * (1 - x ^ 2) - 2 * x * -(2 * x)) / (1 - x ^ 2) ^ 2 -
        (1 / (1 + x) - -1 / (1 - x)) = 4 * x ^ 2 / (1 - x ^ 2) ^ 2 := by
      have : 1 - x ^ 2 = (1 + x) * (1 - x) := by ring
      rw [this]; field_simp; ring
    exact (this : HasDerivAt k _ x).congr_deriv e
  have hmono : MonotoneOn k (Icc 0 u) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc 0 u)
    · intro x hx
      have hx1 : x < 1 := lt_of_le_of_lt hx.2 h1
      have hne : 1 - x ^ 2 ≠ 0 := by nlinarith [hx.1]
      apply ContinuousAt.continuousWithinAt
      apply ContinuousAt.sub
      · exact (continuousAt_const.mul continuousAt_id).div
          (continuousAt_const.sub (continuousAt_id.pow 2)) hne
      · exact (ca_log1 x (by linarith [hx.1])).sub (ca_log2 x hx1)
    · intro x hx
      rw [interior_Icc] at hx
      exact (hd x ⟨hx.1, lt_trans hx.2 h1⟩).differentiableAt.differentiableWithinAt
    · intro x hx
      rw [interior_Icc] at hx
      rw [(hd x ⟨hx.1, lt_trans hx.2 h1⟩).deriv]
      positivity
  have := hmono ⟨le_rfl, h0⟩ ⟨h0, le_rfl⟩ h0
  simp only [k] at this
  norm_num at this
  linarith

/-- n(u) = u Φ'(u) - 2Φ(u) ≥ 0 on [0,1) -/
lemma n_nonneg (u : ℝ) (h0 : 0 ≤ u) (h1 : u < 1) :
    2 * Phi u ≤ u * (Real.log (1 + u) - Real.log (1 - u)) := by
  let n : ℝ → ℝ := fun u => u * (Real.log (1 + u) - Real.log (1 - u)) - 2 * Phi u
  have hd : ∀ x ∈ Ioo (0:ℝ) 1, HasDerivAt n
      (2 * x / (1 - x ^ 2) - (Real.log (1 + x) - Real.log (1 - x))) x := by
    intro x ⟨hx0, hx1⟩
    have := ((hasDerivAt_id x).mul ((hd_log1 x (by linarith)).sub (hd_log2 x hx1))).sub
      ((hasDerivAt_Phi x (by linarith) hx1).const_mul 2)
    have h1' : 1 + x ≠ 0 := by linarith
    have h2' : 1 - x ≠ 0 := by linarith
    have e : 1 * (Real.log (1 + x) - Real.log (1 - x)) + id x * (1 / (1 + x) - -1 / (1 - x)) -
        2 * (Real.log (1 + x) - Real.log (1 - x)) =
        2 * x / (1 - x ^ 2) - (Real.log (1 + x) - Real.log (1 - x)) := by
      have : 1 - x ^ 2 = (1 + x) * (1 - x) := by ring
      rw [this, id]; field_simp; ring
    exact (this : HasDerivAt n _ x).congr_deriv e
  have hmono : MonotoneOn n (Icc 0 u) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc 0 u)
    · intro x hx
      have hx1 : x < 1 := lt_of_le_of_lt hx.2 h1
      apply ContinuousAt.continuousWithinAt
      exact (hasDerivAt_id x |>.mul ((hd_log1 x (by linarith [hx.1])).sub
        (hd_log2 x hx1))).continuousAt.sub
        ((hasDerivAt_Phi x (by linarith [hx.1]) hx1).continuousAt.const_mul 2)
    · intro x hx
      rw [interior_Icc] at hx
      exact (hd x ⟨hx.1, lt_trans hx.2 h1⟩).differentiableAt.differentiableWithinAt
    · intro x hx
      rw [interior_Icc] at hx
      rw [(hd x ⟨hx.1, lt_trans hx.2 h1⟩).deriv]
      have := k_nonneg x hx.1.le (lt_trans hx.2 h1)
      linarith
  have := hmono ⟨le_rfl, h0⟩ ⟨h0, le_rfl⟩ h0
  simp only [n, Phi] at this
  norm_num at this
  unfold Phi
  linarith

lemma Phi_cont : ContinuousOn Phi (Icc 0 1) := by
  unfold Phi
  apply ContinuousOn.add
  · intro x hx
    exact ((continuousAt_const.add continuousAt_id).mul
      (ca_log1 x (by linarith [hx.1]))).continuousWithinAt
  · have : (fun u : ℝ => (1 - u) * Real.log (1 - u)) =
        (fun x => x * Real.log x) ∘ (fun u => 1 - u) := rfl
    rw [this]
    exact (Real.continuous_mul_log.comp (continuous_const.sub continuous_id)).continuousOn

/-- Φ(u) ≤ 2 u² log 2 on [0,1] -/
lemma Phi_le (u : ℝ) (h0 : 0 ≤ u) (h1 : u ≤ 1) : Phi u ≤ 2 * Real.log 2 * u ^ 2 := by
  rcases h0.eq_or_lt with rfl | hu0
  · simp [Phi]
  let m : ℝ → ℝ := fun u => Phi u / u ^ 2
  have hdm : ∀ x ∈ Ioo u 1, HasDerivAt m (((Real.log (1 + x) - Real.log (1 - x)) * x ^ 2 -
      Phi x * (2 * x)) / (x ^ 2) ^ 2) x := by
    intro x hx
    have hx0 : 0 < x := lt_trans hu0 hx.1
    have hp : HasDerivAt (fun u : ℝ => u ^ 2) (2 * x) x := by
      simpa using hasDerivAt_pow 2 x
    exact ((hasDerivAt_Phi x (by linarith) hx.2).div hp (by positivity) : HasDerivAt m _ x)
  have hmono : MonotoneOn m (Icc u 1) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc u 1)
    · apply ContinuousOn.div (Phi_cont.mono (Icc_subset_Icc hu0.le le_rfl))
        (continuousOn_id.pow 2)
      intro x hx; have : 0 < x := lt_of_lt_of_le hu0 hx.1; exact pow_ne_zero 2 this.ne'
    · intro x hx
      rw [interior_Icc] at hx
      exact (hdm x hx).differentiableAt.differentiableWithinAt
    · intro x hx
      rw [interior_Icc] at hx
      have hx0 : 0 < x := lt_trans hu0 hx.1
      rw [(hdm x hx).deriv]
      have := n_nonneg x hx0.le hx.2
      apply div_nonneg _ (by positivity)
      nlinarith [sq_nonneg x]
  have := hmono ⟨le_rfl, h1⟩ ⟨h1, le_rfl⟩ h1
  simp only [m, Phi] at this
  norm_num at this
  have hu2 : 0 < u ^ 2 := by positivity
  rw [div_le_iff₀ hu2] at this
  unfold Phi
  have e : (1 + 1 : ℝ) * Real.log (1 + 1) = 2 * Real.log 2 := by norm_num
  nlinarith

/-- the visibility gap inequality -/
lemma gap_pos (u : ℝ) (h0 : 0 < u) (h1 : u < 1) : Phi u / 2 < Real.log (1 + u ^ 2) := by
  have hw0 : 0 < u ^ 2 := by positivity
  have hw1 : u ^ 2 < 1 := by nlinarith
  have hc := strictConcaveOn_log_Ioi.2 (show (1:ℝ) ∈ Ioi 0 by norm_num)
    (show (2:ℝ) ∈ Ioi 0 by norm_num) (by norm_num) (show 0 < 1 - u ^ 2 by linarith) hw0
    (by ring)
  simp only [smul_eq_mul, Real.log_one, mul_zero, zero_add] at hc
  have e : (1 - u ^ 2) * 1 + u ^ 2 * 2 = 1 + u ^ 2 := by ring
  rw [e] at hc
  have := Phi_le u h0.le h1.le
  linarith

end X6P41

open scoped Matrix ComplexConjugate ComplexOrder
open QAlgorithms QAlgorithms.Papers.Independent.Information100.P41

namespace X6P41

open Matrix

section
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] in

lemma two_selfAdjoint (P : Matrix ι ι ℂ) (hPh : Pᴴ = P) (a b : ℝ) :
    IsSelfAdjoint ((a : ℂ) • P + (b : ℂ) • (1 - P)) := by
  show ((a : ℂ) • P + (b : ℂ) • (1 - P))ᴴ = _
  rw [conjTranspose_add, conjTranspose_smul, conjTranspose_smul, conjTranspose_sub,
    conjTranspose_one, hPh]
  simp

lemma spectrum_two (P : Matrix ι ι ℂ) (hP : P * P = P) (a b : ℝ) (r : ℝ)
    (hr : r ∈ spectrum ℝ ((a : ℂ) • P + (b : ℂ) • (1 - P))) : r = a ∨ r = b := by
  by_contra h
  push Not at h
  obtain ⟨ha, hb⟩ := h
  apply (spectrum.mem_iff.1 hr)
  have ha' : ((r : ℂ) - a) ≠ 0 := by
    rw [sub_ne_zero]; exact_mod_cast ha
  have hb' : ((r : ℂ) - b) ≠ 0 := by
    rw [sub_ne_zero]; exact_mod_cast hb
  set Y : Matrix ι ι ℂ := ((r : ℂ) - a)⁻¹ • P + ((r : ℂ) - b)⁻¹ • (1 - P)
  have hX : algebraMap ℝ (Matrix ι ι ℂ) r - ((a : ℂ) • P + (b : ℂ) • (1 - P)) =
      ((r : ℂ) - a) • P + ((r : ℂ) - b) • (1 - P) := by
    rw [Algebra.algebraMap_eq_smul_one]
    rw [show (r • (1 : Matrix ι ι ℂ)) = (r : ℂ) • (1 : Matrix ι ι ℂ) by
      rw [← Complex.coe_smul]]
    simp only [sub_smul, smul_sub]
    abel
  rw [hX]
  have hP1 : P * (1 - P) = 0 := by rw [mul_sub, mul_one, hP, sub_self]
  have hP2 : (1 - P) * P = 0 := by rw [sub_mul, one_mul, hP, sub_self]
  have hP3 : (1 - P) * (1 - P) = 1 - P := by
    rw [sub_mul, one_mul, hP1, sub_zero]
  refine isUnit_iff_exists.2 ⟨Y, ?_, ?_⟩
  · simp only [Y, add_mul, mul_add, smul_mul_smul, hP, hP1, hP2, hP3, smul_zero, add_zero,
      zero_add, mul_inv_cancel₀ ha', mul_inv_cancel₀ hb', one_smul]
    abel
  · simp only [Y, add_mul, mul_add, smul_mul_smul, hP, hP1, hP2, hP3, smul_zero, add_zero,
      zero_add, inv_mul_cancel₀ ha', inv_mul_cancel₀ hb', one_smul]
    abel

lemma cfc_two (P : Matrix ι ι ℂ) (hP : P * P = P) (hPh : Pᴴ = P) (a b : ℝ) (f : ℝ → ℝ) :
    cfc f ((a : ℂ) • P + (b : ℂ) • (1 - P)) = (f a : ℂ) • P + (f b : ℂ) • (1 - P) := by
  have hsa := two_selfAdjoint P hPh a b
  rcases eq_or_ne a b with hab | hab
  · subst hab
    have : (a : ℂ) • P + (a : ℂ) • (1 - P) = algebraMap ℝ (Matrix ι ι ℂ) a := by
      rw [← smul_add, add_sub_cancel, Algebra.algebraMap_eq_smul_one, ← Complex.coe_smul]
    rw [this, cfc_algebraMap, Algebra.algebraMap_eq_smul_one, ← smul_add, add_sub_cancel,
      ← Complex.coe_smul]
  · set α : ℝ := (f a - f b) / (a - b)
    set β : ℝ := (a * f b - b * f a) / (a - b)
    have hab' : a - b ≠ 0 := sub_ne_zero.2 hab
    have hcongr : cfc f ((a : ℂ) • P + (b : ℂ) • (1 - P)) =
        cfc (fun x => α * x + β) ((a : ℂ) • P + (b : ℂ) • (1 - P)) := by
      apply cfc_congr
      intro r hr
      rcases spectrum_two P hP a b r hr with h | h
      · subst h; simp only [α, β]; field_simp; ring
      · subst h; simp only [α, β]; field_simp; ring
    rw [hcongr, cfc_add (a := (a : ℂ) • P + (b : ℂ) • (1 - P)) (fun x => α * x) (fun _ => β),
      cfc_const_mul α (fun x => x) ((a : ℂ) • P + (b : ℂ) • (1 - P)),
      cfc_id' (R := ℝ) (a := (a : ℂ) • P + (b : ℂ) • (1 - P)),
      cfc_const β ((a : ℂ) • P + (b : ℂ) • (1 - P))]
    rw [Algebra.algebraMap_eq_smul_one]
    rw [show (β • (1 : Matrix ι ι ℂ)) = (β : ℂ) • (1 : Matrix ι ι ℂ) by
      rw [← Complex.coe_smul]]
    rw [show (α • ((a : ℂ) • P + (b : ℂ) • (1 - P))) =
        (α : ℂ) • ((a : ℂ) • P + (b : ℂ) • (1 - P)) by rw [← Complex.coe_smul]]
    have hab'' : (a : ℂ) - b ≠ 0 := by rw [sub_ne_zero]; exact_mod_cast hab
    have e1 : (f a : ℂ) = α * a + β := by
      simp only [α, β]; push_cast; field_simp; ring
    have e2 : (f b : ℂ) = α * b + β := by
      simp only [α, β]; push_cast; field_simp; ring
    rw [e1, e2]
    simp only [smul_add, smul_sub, smul_smul, add_smul, sub_smul]
    abel


lemma trace_cfc_herm {A : Matrix ι ι ℂ} (hA : A.IsHermitian) (f : ℝ → ℝ) :
    (cfc f A).trace = ∑ i, ((f (hA.eigenvalues i) : ℝ) : ℂ) := by
  rw [hA.cfc_eq, Matrix.IsHermitian.cfc, Unitary.conjStarAlgAut_apply, Matrix.trace_mul_cycle,
    Unitary.star_mul_self_of_mem (hA.eigenvectorUnitary).2, one_mul,
    Matrix.trace_diagonal]
  rfl

lemma entropy_nonneg {d : ℕ} (R : Matrix (Fin d) (Fin d) ℂ) (hR : R.PosSemidef) (htr : R.trace = 1) :
    0 ≤ entropy R := by
  have hA := hR.1
  unfold entropy vnEntropy
  rw [trace_cfc_herm hA]
  have hsum : ∑ i, hA.eigenvalues i = 1 := by
    have := hA.trace_eq_sum_eigenvalues
    rw [htr] at this
    have h2 := congrArg Complex.re this
    simpa using h2.symm
  have hnn := hR.eigenvalues_nonneg
  have hle : ∀ i, hA.eigenvalues i ≤ 1 := by
    intro i
    rw [← hsum]
    exact Finset.single_le_sum (fun j _ => hnn j) (Finset.mem_univ i)
  have : ∀ i, hA.eigenvalues i * Real.logb 2 (hA.eigenvalues i) ≤ 0 := by
    intro i
    exact mul_nonpos_of_nonneg_of_nonpos (hnn i)
      (Real.logb_nonpos (by norm_num) (hnn i) (hle i))
  rw [Complex.re_sum]
  simp only [Complex.ofReal_re]
  have := Finset.sum_nonpos (s := Finset.univ) (fun i _ => this i)
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  nlinarith

/-- entropy of a two-level spectral form -/
lemma entropy_two {d : ℕ} (P : Matrix (Fin d) (Fin d) ℂ) (hP : P * P = P) (hPh : Pᴴ = P) (htP : P.trace = 1)
    (ht1 : (1 - P).trace = 1) (a b : ℝ) :
    entropy ((a : ℂ) • P + (b : ℂ) • (1 - P)) = -(a * Real.log a + b * Real.log b) := by
  unfold entropy vnEntropy
  rw [cfc_two P hP hPh a b]
  rw [Matrix.trace_add, Matrix.trace_smul, Matrix.trace_smul, htP, ht1]
  simp only [smul_eq_mul, mul_one, Complex.add_re, Complex.ofReal_re]
  have h2 : Real.log 2 ≠ 0 := (Real.log_pos (by norm_num)).ne'
  unfold Real.logb
  field_simp

end

lemma jc_out (eta nbar theta : ℝ) :
    jcOutput eta nbar theta = !![((1 - nbar * Real.sin theta ^ 2 : ℝ) : ℂ),
      Complex.I * ((eta * Real.sqrt (nbar * (1 - nbar)) * Real.sin theta : ℝ) : ℂ);
      -Complex.I * ((eta * Real.sqrt (nbar * (1 - nbar)) * Real.sin theta : ℝ) : ℂ),
      ((nbar * Real.sin theta ^ 2 : ℝ) : ℂ)] := by
  have hcs := Real.sin_sq_add_cos_sq theta
  ext i j
  fin_cases i <;> fin_cases j <;>
  · simp [jcOutput, traceRight, Matrix.mul_apply, Fin.sum_univ_two,
      jcIsometry, fieldState, Matrix.conjTranspose_apply, -Complex.ofReal_sin, -Complex.ofReal_cos,
      Complex.ext_iff]
    try simp only [← Complex.ofReal_pow, Complex.ofReal_re, Complex.ofReal_im, or_true, and_true]
    try ring_nf
    try linear_combination (-nbar) * hcs
    try linear_combination nbar * hcs

lemma anomaly_formula (r0 b : ℝ) (h0 : r0 ≠ 0) (h1 : 1 - r0 ≠ 0) :
    outputAnomaly (!![(r0 : ℂ), Complex.I * (b : ℂ); -Complex.I * (b : ℂ), ((1 - r0 : ℝ) : ℂ)])
      (!![(r0 : ℂ), Complex.I * (b : ℂ); -Complex.I * (b : ℂ), ((1 - r0 : ℝ) : ℂ)]) =
      ((b ^ 2 / (r0 * (1 - r0)) : ℝ) : ℂ) := by
  set r1 := 1 - r0 with hr1
  set M : Matrix (Fin 2) (Fin 2) ℂ := !![(r0 : ℂ), Complex.I * (b : ℂ); -Complex.I * (b : ℂ), (r1 : ℂ)]
  have hd : Matrix.diagonal (Matrix.diag M) = Matrix.diagonal ![(r0 : ℂ), (r1 : ℂ)] := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [M]
  have h0' : (r0 : ℂ) ≠ 0 := by exact_mod_cast h0
  have h1' : (r1 : ℂ) ≠ 0 := by exact_mod_cast h1
  have hinv : (Matrix.diagonal ![(r0 : ℂ), (r1 : ℂ)])⁻¹ =
      Matrix.diagonal ![(r0 : ℂ)⁻¹, (r1 : ℂ)⁻¹] := by
    apply Matrix.inv_eq_left_inv
    rw [Matrix.diagonal_mul_diagonal]
    ext i j; fin_cases i <;> fin_cases j <;> simp [h0', h1']
  unfold outputAnomaly
  rw [hd, hinv]
  have key : ((b ^ 2 / (r0 * r1) : ℝ) : ℂ) = (r0 : ℂ)⁻¹ * (b : ℂ) ^ 2 + (r1 : ℂ)⁻¹ * (b : ℂ) ^ 2 := by
    have hr1' : (r1 : ℂ) = 1 - r0 := by rw [hr1]; push_cast; ring
    have h1'' : (1 - r0 : ℂ) ≠ 0 := by rw [← hr1']; exact h1'
    push_cast
    rw [hr1']
    field_simp
    ring
  rw [key]
  simp [M, Matrix.trace, Fin.sum_univ_two, Matrix.mul_apply, Matrix.diagonal_apply]
  ring_nf
  rw [Complex.I_sq]
  ring


end X6P41

open scoped Matrix ComplexConjugate ComplexOrder
open QAlgorithms QAlgorithms.Papers.Independent.Information100.P41

namespace X6P41

open Matrix

def Pm : Matrix (Fin 2) (Fin 2) ℂ := !![1 / 2, Complex.I / 2; -Complex.I / 2, 1 / 2]

lemma Pm_idem : Pm * Pm = Pm := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [Pm, Matrix.mul_apply, Fin.sum_univ_two] <;> ring_nf <;> simp [Complex.I_sq] <;> ring

lemma Pm_herm : Pmᴴ = Pm := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [Pm, Matrix.conjTranspose_apply] <;> ring

lemma Pm_tr : Pm.trace = 1 := by
  simp [Pm, Matrix.trace, Fin.sum_univ_two]; norm_num

lemma Pm_tr1 : (1 - Pm).trace = 1 := by
  rw [Matrix.trace_sub, Pm_tr, Matrix.trace_one]; simp; norm_num

lemma sqrt_quarter : Real.sqrt (1 / 2 * (1 - 1 / 2)) = 1 / 2 := by
  rw [show (1:ℝ) / 2 * (1 - 1 / 2) = (1 / 2) ^ 2 by norm_num]
  exact Real.sqrt_sq (by norm_num)

lemma out_half (eta : ℝ) :
    jcOutput eta (1 / 2) (Real.pi / 2) =
      (((1 + eta) / 2 : ℝ) : ℂ) • Pm + (((1 - eta) / 2 : ℝ) : ℂ) • (1 - Pm) := by
  rw [jc_out, Real.sin_pi_div_two, sqrt_quarter]
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [Pm] <;> push_cast <;> ring

lemma diag_half (eta : ℝ) :
    Matrix.diagonal (Matrix.diag (jcOutput eta (1 / 2) (Real.pi / 2))) =
      (((1 / 2 : ℝ)) : ℂ) • Pm + (((1 / 2 : ℝ)) : ℂ) • (1 - Pm) := by
  rw [out_half]
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [Pm, Matrix.diagonal_apply] <;> push_cast <;> ring

lemma coherence_ground : coherence groundState = 0 := by
  unfold groundState referenceProjector
  simp [coherence]

lemma plogp (eta : ℝ) (h0 : 0 ≤ eta) (h1 : eta ≤ 1) :
    (1 + eta) / 2 * Real.log ((1 + eta) / 2) + (1 - eta) / 2 * Real.log ((1 - eta) / 2) =
      Phi eta / 2 - Real.log 2 := by
  unfold Phi
  rw [Real.log_div (by linarith) (by norm_num)]
  rcases h1.eq_or_lt with rfl | h1'
  · simp; ring
  · rw [Real.log_div (by linarith) (by norm_num)]; ring

lemma change_half (eta : ℝ) (h0 : 0 ≤ eta) (h1 : eta ≤ 1) :
    jcChange eta (1 / 2) (Real.pi / 2) = Phi eta / 2 := by
  unfold jcChange
  rw [coherence_ground]
  unfold coherence
  rw [diag_half, out_half,
    entropy_two Pm Pm_idem Pm_herm Pm_tr Pm_tr1, entropy_two Pm Pm_idem Pm_herm Pm_tr Pm_tr1]
  have := plogp eta h0 h1
  rw [show (1:ℝ) / 2 = 2⁻¹ by norm_num, Real.log_inv]
  linarith

lemma anomaly_half (eta : ℝ) :
    jcAnomaly eta (1 / 2) (Real.pi / 2) = ((eta ^ 2 : ℝ) : ℂ) := by
  unfold jcAnomaly
  rw [jc_out, Real.sin_pi_div_two, sqrt_quarter]
  have := anomaly_formula (1 - 1 / 2 * 1 ^ 2) (eta * (1 / 2) * 1) (by norm_num) (by norm_num)
  rw [show (1:ℝ) - (1 - 1 / 2 * 1 ^ 2) = 1 / 2 * 1 ^ 2 by ring] at this
  rw [this]
  congr 1
  field_simp
  ring

lemma Phi_zero : Phi 0 = 0 := by simp [Phi]
lemma Phi_one : Phi 1 = 2 * Real.log 2 := by
  simp [Phi]; norm_num

end X6P41

open X6P41 in
theorem solution :
    (∀ eta : ℝ, 0 ≤ eta → eta ≤ 1 →
      jcAnomaly eta (1 / 2) (Real.pi / 2) = ((eta ^ 2 : ℝ) : ℂ)) ∧
    MonotoneOn (fun eta : ℝ => (jcAnomaly eta (1 / 2) (Real.pi / 2)).re) (Set.Icc 0 1) ∧
    (∀ eta : ℝ, 0 < eta → eta < 1 → 0 < visibilityGap eta) ∧
    visibilityGap 0 = 0 ∧ visibilityGap 1 = 0 ∧
    jcChange 0 (1 / 2) (Real.pi / 2) = 0 := by
  refine ⟨fun eta _ _ => anomaly_half eta, ?_, ?_, ?_, ?_, ?_⟩
  · intro a ha b hb hab
    simp only [anomaly_half, Complex.ofReal_re]
    exact pow_le_pow_left₀ ha.1 hab 2
  · intro eta h0 h1
    unfold visibilityGap
    rw [anomaly_half, Complex.ofReal_re, change_half eta h0.le h1.le]
    have := gap_pos eta h0 h1
    linarith
  · unfold visibilityGap
    rw [anomaly_half, Complex.ofReal_re, change_half 0 le_rfl zero_le_one, Phi_zero]
    simp
  · unfold visibilityGap
    rw [anomaly_half, Complex.ofReal_re, change_half 1 zero_le_one le_rfl, Phi_one]
    norm_num
  · rw [change_half 0 le_rfl zero_le_one, Phi_zero]; simp
