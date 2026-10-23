-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Information100.P41.anomaly_coheringPower_bound
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T14:03:42.096982+00:00
-- url     : https://prove2.me/submissions/abf3ced7-f449-4659-a8b1-b98fc165a93f

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

open scoped Matrix ComplexConjugate ComplexOrder
open QAlgorithms QAlgorithms.Papers.Independent.Information100.P41

namespace X6P41

open Matrix

set_option maxHeartbeats 1000000 in
lemma anom_gen (eta nbar theta : ℝ)
    (heta : 0 ≤ eta ∧ eta ≤ 1) (hnbar : 0 < nbar ∧ nbar < 1)
    (htheta : Real.sin theta ≠ 0) :
    jcAnomaly eta nbar theta =
      ((eta ^ 2 * (1 - nbar) / (1 - nbar * Real.sin theta ^ 2) : ℝ) : ℂ) ∧
    jcAnomaly eta nbar theta =
      ((‖jcOutput eta nbar theta 0 1‖ ^ 2 /
        ((jcOutput eta nbar theta 0 0).re * (jcOutput eta nbar theta 1 1).re) : ℝ) : ℂ) := by
  have hs2 : 0 < Real.sin theta ^ 2 := by positivity
  have hs1 : Real.sin theta ^ 2 ≤ 1 := by
    nlinarith [Real.sin_sq_add_cos_sq theta, sq_nonneg (Real.cos theta)]
  have hr0 : 0 < 1 - nbar * Real.sin theta ^ 2 := by nlinarith
  have hr1 : 0 < nbar * Real.sin theta ^ 2 := by nlinarith
  have e1 : 1 - (1 - nbar * Real.sin theta ^ 2) = nbar * Real.sin theta ^ 2 := by ring
  have hA : jcAnomaly eta nbar theta =
      (((eta * Real.sqrt (nbar * (1 - nbar)) * Real.sin theta) ^ 2 /
        ((1 - nbar * Real.sin theta ^ 2) * (nbar * Real.sin theta ^ 2)) : ℝ) : ℂ) := by
    unfold jcAnomaly
    rw [jc_out]
    have := anomaly_formula (1 - nbar * Real.sin theta ^ 2)
      (eta * Real.sqrt (nbar * (1 - nbar)) * Real.sin theta) hr0.ne' (by rw [e1]; exact hr1.ne')
    rw [e1] at this
    exact this
  have hb2 : (eta * Real.sqrt (nbar * (1 - nbar)) * Real.sin theta) ^ 2 =
      eta ^ 2 * (nbar * (1 - nbar)) * Real.sin theta ^ 2 := by
    rw [mul_pow, mul_pow, Real.sq_sqrt (by nlinarith)]
  refine ⟨?_, ?_⟩
  · have hn : nbar ≠ 0 := hnbar.1.ne'
    rw [hA, hb2]; congr 1; field_simp
  · rw [hA, jc_out]
    simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one, Complex.ofReal_re]
    rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs, sq_abs]


lemma posSemidef_of_forall {ι : Type*} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι ℂ)
    (h : ∀ v : ι → ℂ, 0 ≤ star v ⬝ᵥ (M *ᵥ v)) : M.PosSemidef := by
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ h
  rw [← Matrix.isSymmetric_toEuclideanLin_iff, LinearMap.isSymmetric_iff_inner_map_self_real]
  intro v
  have hz := h v.ofLp
  have hre : (star v.ofLp ⬝ᵥ (M *ᵥ v.ofLp)).im = 0 := (Complex.nonneg_iff.mp hz).2.symm
  have hin : inner ℂ (M.toEuclideanLin v) v = conj (star v.ofLp ⬝ᵥ (M *ᵥ v.ofLp)) := by
    rw [← inner_conj_symm, EuclideanSpace.inner_eq_star_dotProduct, Matrix.toEuclideanLin_apply,
      dotProduct_comm]
  rw [hin, Complex.conj_conj]
  apply Complex.ext <;> simp [hre]

lemma binary_le (p q : ℝ) (hp : 0 ≤ p) (hq : 0 ≤ q) (hs : p + q = 1) :
    -(p * Real.log p + q * Real.log q) ≤ Real.log 2 := by
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have key : ∀ x : ℝ, 0 ≤ x → -(x * Real.log x) - x * Real.log 2 ≤ 1 / 2 - x := by
    intro x hx
    rcases hx.eq_or_lt with rfl | hx
    · simp
    have := Real.log_le_sub_one_of_pos (show 0 < 1 / (2 * x) by positivity)
    rw [Real.log_div (by norm_num) (by positivity), Real.log_one, Real.log_mul (by norm_num) hx.ne']
      at this
    have := mul_le_mul_of_nonneg_left this hx.le
    have e : x * (1 / (2 * x) - 1) = 1 / 2 - x := by field_simp
    rw [e] at this
    nlinarith
  have := key p hp
  have := key q hq
  have : (p + q) * Real.log 2 = Real.log 2 := by rw [hs, one_mul]
  nlinarith

lemma quad2 (r0 r1 β a c : ℝ) (h0 : 0 ≤ r0) (h1 : 0 ≤ r1) (hb : β ^ 2 ≤ r0 * r1) :
    0 ≤ r0 * a ^ 2 - 2 * β * a * c + r1 * c ^ 2 := by
  rcases h0.eq_or_lt with rfl | h0'
  · have : β = 0 := by nlinarith [sq_nonneg β]
    subst this; nlinarith [sq_nonneg c]
  · have : 0 ≤ r0 * (r0 * a ^ 2 - 2 * β * a * c + r1 * c ^ 2) := by
      nlinarith [sq_nonneg (r0 * a - β * c), sq_nonneg c]
    exact (mul_nonneg_iff_of_pos_left h0').mp this

end X6P41

open scoped Matrix ComplexConjugate ComplexOrder
open QAlgorithms QAlgorithms.Papers.Independent.Information100.P41

namespace X6P41

open Matrix

def E0 : Matrix (Fin 2) (Fin 2) ℂ := Matrix.diagonal ![1, 0]

lemma E0_idem : E0 * E0 = E0 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [E0]
lemma E0_herm : E0ᴴ = E0 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [E0, Matrix.conjTranspose_apply]
lemma E0_tr : E0.trace = 1 := by simp [E0, Matrix.trace, Fin.sum_univ_two]
lemma E0_tr1 : (1 - E0).trace = 1 := by
  rw [Matrix.trace_sub, E0_tr, Matrix.trace_one]; simp; norm_num

lemma diag_gen (eta b theta : ℝ) :
    Matrix.diagonal (Matrix.diag (jcOutput eta b theta)) =
      (((1 - b * Real.sin theta ^ 2) : ℝ) : ℂ) • E0 + (((b * Real.sin theta ^ 2) : ℝ) : ℂ) • (1 - E0) := by
  rw [jc_out]
  ext i j; fin_cases i <;> fin_cases j <;> simp [E0, Matrix.diagonal_apply]

lemma trace_gen (eta b theta : ℝ) : (jcOutput eta b theta).trace = 1 := by
  rw [jc_out]; simp [Matrix.trace, Fin.sum_univ_two]

lemma psd_gen (eta b theta : ℝ) (he : 0 ≤ eta ∧ eta ≤ 1) (hb : 0 ≤ b ∧ b ≤ 1) :
    (jcOutput eta b theta).PosSemidef := by
  rw [jc_out]
  set s := Real.sin theta
  set β := eta * Real.sqrt (b * (1 - b)) * s
  have hs1 : s ^ 2 ≤ 1 := by
    nlinarith [Real.sin_sq_add_cos_sq theta, sq_nonneg (Real.cos theta)]
  have hr0 : 0 ≤ 1 - b * s ^ 2 := by nlinarith [sq_nonneg s]
  have hr1 : 0 ≤ b * s ^ 2 := by nlinarith [sq_nonneg s]
  have hβ : β ^ 2 ≤ (1 - b * s ^ 2) * (b * s ^ 2) := by
    simp only [β]
    rw [mul_pow, mul_pow, Real.sq_sqrt (by nlinarith)]
    have : eta ^ 2 ≤ 1 := by nlinarith
    have hbb : 0 ≤ b * (1 - b) := by nlinarith
    nlinarith [mul_nonneg (mul_nonneg hbb (sq_nonneg s)) (sub_nonneg.mpr this),
      mul_nonneg (mul_nonneg hb.1 hb.1) (mul_nonneg (sq_nonneg s) (sub_nonneg.mpr hs1))]
  apply posSemidef_of_forall
  intro v
  have hq1 := quad2 (1 - b * s ^ 2) (b * s ^ 2) β (v 0).re (v 1).im hr0 hr1 hβ
  have hq2 := quad2 (1 - b * s ^ 2) (b * s ^ 2) (-β) (v 0).im (v 1).re hr0 hr1 (by simpa using hβ)
  rw [Complex.nonneg_iff]
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Complex.mul_re, Complex.mul_im]
  simp only [← Complex.ofReal_pow, Complex.ofReal_re, Complex.ofReal_im]
  constructor
  · nlinarith [hq1, hq2]
  · ring

end X6P41

open scoped Matrix ComplexConjugate ComplexOrder
open QAlgorithms QAlgorithms.Papers.Independent.Information100.P41

namespace X6P41

open Matrix

variable {d : ℕ}

lemma spec_entry {R : Matrix (Fin d) (Fin d) ℂ} (hA : R.IsHermitian) (x y : Fin d) :
    R x y = ∑ i, (hA.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℂ) x i * (hA.eigenvalues i : ℂ) *
      star ((hA.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℂ) y i) := by
  conv_lhs => rw [hA.spectral_theorem]
  rw [Unitary.conjStarAlgAut_apply, Matrix.mul_apply]
  apply Finset.sum_congr rfl
  intro i _
  rw [Matrix.mul_diagonal, Matrix.star_apply]
  rfl

lemma row_sum {R : Matrix (Fin d) (Fin d) ℂ} (hA : R.IsHermitian) (x : Fin d) :
    ∑ i, ‖(hA.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℂ) x i‖ ^ 2 = 1 := by
  set U : Matrix (Fin d) (Fin d) ℂ := (hA.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℂ)
  have hU : U * star U = 1 := Unitary.mul_star_self_of_mem (hA.eigenvectorUnitary).2
  have h : (U * star U) x x = (1 : Matrix (Fin d) (Fin d) ℂ) x x := by rw [hU]
  rw [Matrix.mul_apply, Matrix.one_apply_eq] at h
  have h2 := congrArg Complex.re h
  simp only [Matrix.star_apply, Complex.re_sum, Complex.one_re] at h2
  rw [← h2]
  apply Finset.sum_congr rfl
  intro i _
  rw [RCLike.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  exact (Complex.ofReal_re _).symm

lemma col_sum {R : Matrix (Fin d) (Fin d) ℂ} (hA : R.IsHermitian) (i : Fin d) :
    ∑ x, ‖(hA.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℂ) x i‖ ^ 2 = 1 := by
  set U : Matrix (Fin d) (Fin d) ℂ := (hA.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℂ)
  have hU : star U * U = 1 := Unitary.star_mul_self_of_mem (hA.eigenvectorUnitary).2
  have h : (star U * U) i i = (1 : Matrix (Fin d) (Fin d) ℂ) i i := by rw [hU]
  rw [Matrix.mul_apply, Matrix.one_apply_eq] at h
  have h2 := congrArg Complex.re h
  simp only [Matrix.star_apply, Complex.re_sum, Complex.one_re] at h2
  rw [← h2]
  apply Finset.sum_congr rfl
  intro x _
  rw [RCLike.star_def, mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  exact (Complex.ofReal_re _).symm

lemma diag_re {R : Matrix (Fin d) (Fin d) ℂ} (hA : R.IsHermitian) (x : Fin d) :
    (R x x).re = ∑ i, ‖(hA.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℂ) x i‖ ^ 2 *
      hA.eigenvalues i := by
  rw [spec_entry hA, Complex.re_sum]
  apply Finset.sum_congr rfl
  intro i _
  have : (hA.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℂ) x i * (hA.eigenvalues i : ℂ) *
      star ((hA.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℂ) x i) =
      ((‖(hA.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℂ) x i‖ ^ 2 * hA.eigenvalues i : ℝ) : ℂ) := by
    rw [mul_comm _ (star _), ← mul_assoc, RCLike.star_def, mul_comm (conj _), Complex.mul_conj,
      Complex.normSq_eq_norm_sq]
    push_cast; ring
  rw [this, Complex.ofReal_re]

lemma sq_diag_re {R : Matrix (Fin d) (Fin d) ℂ} (hA : R.IsHermitian) (x : Fin d) :
    ((R * R) x x).re = ∑ i, ‖(hA.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℂ) x i‖ ^ 2 *
      hA.eigenvalues i ^ 2 := by
  set U : Matrix (Fin d) (Fin d) ℂ := (hA.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℂ)
  have hsp : R = U * Matrix.diagonal (RCLike.ofReal ∘ hA.eigenvalues) * star U := by
    conv_lhs => rw [hA.spectral_theorem]
    rfl
  have hUU : star U * U = 1 := Unitary.star_mul_self_of_mem (hA.eigenvectorUnitary).2
  have hRR : R * R = U * Matrix.diagonal (fun i => ((hA.eigenvalues i ^ 2 : ℝ) : ℂ)) * star U := by
    conv_lhs => rw [hsp]
    have : U * Matrix.diagonal (RCLike.ofReal ∘ hA.eigenvalues) * star U *
        (U * Matrix.diagonal (RCLike.ofReal ∘ hA.eigenvalues) * star U) =
        U * (Matrix.diagonal (RCLike.ofReal ∘ hA.eigenvalues) * (star U * U) *
          Matrix.diagonal (RCLike.ofReal ∘ hA.eigenvalues)) * star U := by
      simp only [Matrix.mul_assoc]
    rw [this, hUU, Matrix.mul_one, Matrix.diagonal_mul_diagonal]
    congr 3
    ext i; simp [sq]
  rw [hRR, Matrix.mul_apply, Complex.re_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Matrix.mul_diagonal, Matrix.star_apply]
  have : U x i * ((hA.eigenvalues i ^ 2 : ℝ) : ℂ) * star (U x i) =
      ((‖U x i‖ ^ 2 * hA.eigenvalues i ^ 2 : ℝ) : ℂ) := by
    rw [mul_comm _ (star _), ← mul_assoc, RCLike.star_def, mul_comm (conj _), Complex.mul_conj,
      Complex.normSq_eq_norm_sq]
    push_cast; ring
  rw [this, Complex.ofReal_re]

lemma entropy_spec {R : Matrix (Fin d) (Fin d) ℂ} (hA : R.IsHermitian) :
    entropy R = -∑ i, hA.eigenvalues i * Real.log (hA.eigenvalues i) := by
  unfold entropy vnEntropy
  rw [trace_cfc_herm hA, Complex.re_sum]
  simp only [Complex.ofReal_re]
  have h2 : Real.log 2 ≠ 0 := (Real.log_pos (by norm_num)).ne'
  unfold Real.logb
  rw [mul_neg, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  field_simp

/-- relative-entropy coherence is at most log tr(D⁻¹ R²) -/
lemma coh_le (R : Matrix (Fin d) (Fin d) ℂ) (hR : R.PosSemidef) (htr : R.trace = 1)
    (hpos : ∀ x, 0 < (R x x).re)
    (hD : entropy (Matrix.diagonal (Matrix.diag R)) = -∑ x, (R x x).re * Real.log (R x x).re) :
    coherence R ≤ Real.log (∑ x, ((R * R) x x).re / (R x x).re) := by
  have hA := hR.1
  set U : Matrix (Fin d) (Fin d) ℂ := (hA.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℂ)
  set lam := hA.eigenvalues
  set σ : Fin d → ℝ := fun x => (R x x).re
  set w : Fin d × Fin d → ℝ := fun p => ‖U p.2 p.1‖ ^ 2 * lam p.1
  have hlam : ∀ i, 0 ≤ lam i := hR.eigenvalues_nonneg
  have hsum : ∑ i, lam i = 1 := by
    have := hA.trace_eq_sum_eigenvalues
    rw [htr] at this
    have h2 := congrArg Complex.re this
    simpa using h2.symm
  have hw0 : ∀ p, 0 ≤ w p := fun p => mul_nonneg (sq_nonneg _) (hlam p.1)
  have hwsum : ∑ p, w p = 1 := by
    rw [← hsum, Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro i _
    simp only [w]
    rw [← Finset.sum_mul, col_sum hA i, one_mul]
  -- coherence as a double sum
  have hC : coherence R = ∑ p, w p * (Real.log (lam p.1) - Real.log (σ p.2)) := by
    unfold coherence
    rw [hD, entropy_spec hA]
    simp only [mul_sub, Finset.sum_sub_distrib]
    have e1 : ∑ p, w p * Real.log (lam p.1) = ∑ i, lam i * Real.log (lam i) := by
      rw [Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro i _
      simp only [w]
      rw [← Finset.sum_mul, ← Finset.sum_mul, col_sum hA i, one_mul]
    have e2 : ∑ p, w p * Real.log (σ p.2) = ∑ x, σ x * Real.log (σ x) := by
      rw [Fintype.sum_prod_type_right]
      apply Finset.sum_congr rfl
      intro x _
      simp only [w, σ]
      rw [← Finset.sum_mul, diag_re hA x]
    rw [e1, e2]
    simp only [σ]
    ring
  -- Jensen
  set t := Finset.univ.filter (fun p : Fin d × Fin d => 0 < w p)
  have hlampos : ∀ p ∈ t, 0 < lam p.1 := by
    intro p hp
    have := (Finset.mem_filter.mp hp).2
    simp only [w] at this
    rcases (hlam p.1).eq_or_lt with h | h
    · rw [← h, mul_zero] at this; exact absurd this (lt_irrefl 0)
    · exact h
  have hσ : ∀ x, 0 < σ x := hpos
  have hJ := (strictConcaveOn_log_Ioi.concaveOn).le_map_sum (t := t) (w := w)
    (p := fun p => lam p.1 / σ p.2) (fun p _ => hw0 p) ?_ ?_
  rotate_left
  · rw [← hwsum]
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro p _ hp
    simp only [t, Finset.mem_filter, Finset.mem_univ, true_and, not_lt] at hp
    exact le_antisymm hp (hw0 p)
  · intro p hp
    exact div_pos (hlampos p hp) (hσ p.2)
  simp only [smul_eq_mul] at hJ
  have l1a : ∑ p ∈ t, w p * (Real.log (lam p.1) - Real.log (σ p.2)) =
      ∑ p, w p * (Real.log (lam p.1) - Real.log (σ p.2)) := by
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro p _ hp
    simp only [t, Finset.mem_filter, Finset.mem_univ, true_and, not_lt] at hp
    rw [le_antisymm hp (hw0 p), zero_mul]
  have l1 : ∑ p, w p * (Real.log (lam p.1) - Real.log (σ p.2)) =
      ∑ p ∈ t, w p * Real.log (lam p.1 / σ p.2) := by
    rw [← l1a]
    apply Finset.sum_congr rfl
    intro p hp
    rw [Real.log_div (hlampos p hp).ne' (hσ p.2).ne']
  have l2a : ∑ p ∈ t, w p * (lam p.1 / σ p.2) = ∑ p, w p * (lam p.1 / σ p.2) := by
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro p _ hp
    simp only [t, Finset.mem_filter, Finset.mem_univ, true_and, not_lt] at hp
    rw [le_antisymm hp (hw0 p), zero_mul]
  have l2 : ∑ p ∈ t, w p * (lam p.1 / σ p.2) = ∑ x, ((R * R) x x).re / (R x x).re := by
    rw [l2a, Fintype.sum_prod_type_right]
    apply Finset.sum_congr rfl
    intro x _
    rw [sq_diag_re hA x, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro i _
    simp only [w, σ, lam, U]
    ring
  rw [hC, l1, ← l2]
  exact hJ

end X6P41

open scoped Matrix ComplexConjugate ComplexOrder
open QAlgorithms QAlgorithms.Papers.Independent.Information100.P41

namespace X6P41

open Matrix Polynomial

variable {d : ℕ}

lemma entropy_diag (v : Fin d → ℝ) :
    entropy (Matrix.diagonal (fun i => (v i : ℂ))) = -∑ i, v i * Real.log (v i) := by
  have hA : (Matrix.diagonal (fun i => (v i : ℂ))).IsHermitian := by
    rw [Matrix.IsHermitian, Matrix.diagonal_conjTranspose]; congr 1; ext i; simp
  rw [entropy_spec hA]
  congr 1
  have h1 := hA.roots_charpoly_eq_eigenvalues
  rw [Matrix.charpoly_diagonal, Polynomial.roots_prod _ _ (by
    simp [Finset.prod_ne_zero_iff, Polynomial.X_sub_C_ne_zero])] at h1
  simp only [Polynomial.roots_X_sub_C] at h1
  have h2 := congrArg (fun s : Multiset ℂ => (s.map (fun z => z.re * Real.log z.re)).sum) h1
  simp only [Multiset.map_map, Function.comp_def, Complex.ofReal_re] at h2
  rw [Finset.sum_eq_multiset_sum, Finset.sum_eq_multiset_sum]
  have e : (Finset.univ.val.bind fun i => ({(v i : ℂ)} : Multiset ℂ)) =
      Finset.univ.val.map (fun i => (v i : ℂ)) := by
    simp [Multiset.bind_singleton]
  simp only [e, Multiset.map_map, Function.comp_def, Complex.ofReal_re] at h2
  exact h2.symm

lemma density_of_channel (rho : Matrix (Fin d) (Fin d) ℂ) (hrho : IsDensityMatrix rho)
    (E : Superop (Fin d) (Fin d)) (hE : IsChannel E) : IsDensityMatrix (E rho) := by
  obtain ⟨m, K, hK, hEK⟩ := hE
  rw [hEK]
  unfold krausApply
  refine ⟨Matrix.posSemidef_sum _ (fun j _ => hrho.1.mul_mul_conjTranspose_same (K j)), ?_⟩
  rw [Matrix.trace_sum]
  have : ∑ j, (K j * rho * (K j)ᴴ).trace = ((∑ j, (K j)ᴴ * K j) * rho).trace := by
    rw [Finset.sum_mul, Matrix.trace_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [Matrix.trace_mul_cycle, Matrix.mul_assoc]
  rw [this, hK, Matrix.one_mul, hrho.2]

lemma diag_real {R : Matrix (Fin d) (Fin d) ℂ} (hA : R.IsHermitian) :
    Matrix.diagonal (Matrix.diag R) = Matrix.diagonal (fun x => (((R x x).re : ℝ) : ℂ)) := by
  congr 1; ext x
  have := hA.apply x x
  apply Complex.ext
  · simp
  · simp only [Matrix.diag_apply, Complex.ofReal_im]
    have h := congrArg Complex.im this
    simp at h; linarith

/-- zero coherence forces a diagonal matrix (KL equality case) -/
lemma coh_zero (R : Matrix (Fin d) (Fin d) ℂ) (hR : R.PosSemidef) (htr : R.trace = 1)
    (hpos : ∀ x, 0 < (R x x).re) (h0 : coherence R = 0) :
    R = Matrix.diagonal (Matrix.diag R) := by
  have hA := hR.1
  set U : Matrix (Fin d) (Fin d) ℂ := (hA.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℂ)
  set lam := hA.eigenvalues
  set σ : Fin d → ℝ := fun x => (R x x).re
  set P : Fin d × Fin d → ℝ := fun p => ‖U p.2 p.1‖ ^ 2 * lam p.1
  set Q : Fin d × Fin d → ℝ := fun p => ‖U p.2 p.1‖ ^ 2 * σ p.2
  have hlam : ∀ i, 0 ≤ lam i := hR.eigenvalues_nonneg
  have hsum : ∑ i, lam i = 1 := by
    have := hA.trace_eq_sum_eigenvalues
    rw [htr] at this
    have h2 := congrArg Complex.re this
    simpa using h2.symm
  have hσsum : ∑ x, σ x = 1 := by
    have h := congrArg Complex.re htr
    simpa [Matrix.trace, Complex.re_sum] using h
  have hPsum : ∑ p, P p = 1 := by
    rw [← hsum, Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro i _
    simp only [P]
    rw [← Finset.sum_mul, col_sum hA i, one_mul]
  have hQsum : ∑ p, Q p = 1 := by
    rw [← hσsum, Fintype.sum_prod_type_right]
    apply Finset.sum_congr rfl
    intro x _
    simp only [Q]
    rw [← Finset.sum_mul, row_sum hA x, one_mul]
  have hD : entropy (Matrix.diagonal (Matrix.diag R)) = -∑ x, (R x x).re * Real.log (R x x).re := by
    rw [diag_real hA, entropy_diag]
  have hC : coherence R = ∑ p, P p * (Real.log (lam p.1) - Real.log (σ p.2)) := by
    unfold coherence
    rw [hD, entropy_spec hA]
    simp only [mul_sub, Finset.sum_sub_distrib]
    have e1 : ∑ p, P p * Real.log (lam p.1) = ∑ i, lam i * Real.log (lam i) := by
      rw [Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro i _
      simp only [P]
      rw [← Finset.sum_mul, ← Finset.sum_mul, col_sum hA i, one_mul]
    have e2 : ∑ p, P p * Real.log (σ p.2) = ∑ x, σ x * Real.log (σ x) := by
      rw [Fintype.sum_prod_type_right]
      apply Finset.sum_congr rfl
      intro x _
      simp only [P, σ]
      rw [← Finset.sum_mul, diag_re hA x]
    rw [e1, e2]
    simp only [σ]
    ring
  -- termwise: P (log λ - log σ) - (P - Q) ≥ 0
  set g : Fin d × Fin d → ℝ := fun p => P p * (Real.log (lam p.1) - Real.log (σ p.2)) - (P p - Q p)
  have hg : ∀ p, 0 ≤ g p := by
    intro p
    simp only [g, P, Q]
    have hσp := hpos p.2
    rcases (hlam p.1).eq_or_lt with h | h
    · rw [← h]; simp; positivity
    · have hl := Real.log_le_sub_one_of_pos (div_pos hσp h)
      rw [Real.log_div hσp.ne' h.ne'] at hl
      have hu : 0 ≤ ‖U p.2 p.1‖ ^ 2 := sq_nonneg _
      have := mul_le_mul_of_nonneg_left hl (mul_nonneg hu h.le)
      have e : ‖U p.2 p.1‖ ^ 2 * lam p.1 * (σ p.2 / lam p.1 - 1) =
          ‖U p.2 p.1‖ ^ 2 * σ p.2 - ‖U p.2 p.1‖ ^ 2 * lam p.1 := by field_simp
      rw [e] at this
      nlinarith
  have hgsum : ∑ p, g p = 0 := by
    simp only [g, Finset.sum_sub_distrib, ← hC, h0, hPsum, hQsum]; ring
  have hg0 : ∀ p, g p = 0 := by
    intro p
    have := (Finset.sum_eq_zero_iff_of_nonneg (fun p _ => hg p)).mp hgsum p (Finset.mem_univ p)
    exact this
  -- consequence: U x i ≠ 0 → λ i = σ x
  have key : ∀ i x, U x i * (lam i : ℂ) = (σ x : ℂ) * U x i := by
    intro i x
    by_cases hU : U x i = 0
    · simp [hU]
    have hu : 0 < ‖U x i‖ ^ 2 := by positivity
    have hgx := hg0 (i, x)
    simp only [g, P, Q] at hgx
    have hσp := hpos x
    rcases (hlam i).eq_or_lt with h | h
    · exfalso
      rw [← h] at hgx
      simp at hgx
      rcases hgx with h1 | h1
      · exact hU h1
      · exact absurd h1 hσp.ne'
    · -- strict log inequality unless σ/λ = 1
      by_contra hne
      have hne' : σ x / lam i ≠ 1 := by
        intro h1
        apply hne
        rw [div_eq_one_iff_eq h.ne'] at h1
        simp only [σ] at h1 ⊢
        rw [h1, mul_comm]
      have hl := Real.log_lt_sub_one_of_pos (div_pos hσp h) hne'
      rw [Real.log_div hσp.ne' h.ne'] at hl
      have := mul_lt_mul_of_pos_left hl (mul_pos hu h)
      have e : ‖U x i‖ ^ 2 * lam i * (σ x / lam i - 1) =
          ‖U x i‖ ^ 2 * σ x - ‖U x i‖ ^ 2 * lam i := by field_simp
      rw [e] at this
      nlinarith
  ext x y
  rw [spec_entry hA x y]
  have hU1 : U * star U = 1 := Unitary.mul_star_self_of_mem (hA.eigenvectorUnitary).2
  have hxy : (U * star U) x y = (1 : Matrix (Fin d) (Fin d) ℂ) x y := by rw [hU1]
  rw [Matrix.mul_apply] at hxy
  calc ∑ i, U x i * (lam i : ℂ) * star (U y i) = ∑ i, (σ x : ℂ) * (U x i * star (U y i)) := by
        apply Finset.sum_congr rfl; intro i _
        change U x i * ((hA.eigenvalues i : ℝ) : ℂ) * star (U y i) = _
        rw [key i x]; ring
    _ = (σ x : ℂ) * (1 : Matrix (Fin d) (Fin d) ℂ) x y := by
        rw [← Finset.mul_sum]; congr 1
    _ = Matrix.diagonal (Matrix.diag R) x y := by
        rw [diag_real hA]
        by_cases h : x = y
        · subst h; simp [σ]
        · simp [h]

end X6P41

open scoped Matrix ComplexConjugate ComplexOrder
open QAlgorithms QAlgorithms.Papers.Independent.Information100.P41

namespace X6P41

open Matrix Set

/-- (λ-σ)²/2 ≤ λ(log λ - log σ) - (λ - σ) on (0,1]² -/
lemma kl_quad (l s : ℝ) (hl0 : 0 < l) (hl1 : l ≤ 1) (hs0 : 0 < s) (hs1 : s ≤ 1) :
    (l - s) ^ 2 / 2 ≤ l * (Real.log l - Real.log s) - (l - s) := by
  let f : ℝ → ℝ := fun t => t * (Real.log t - Real.log s) - (t - s) - (t - s) ^ 2 / 2
  let f' : ℝ → ℝ := fun t => Real.log t - Real.log s - (t - s)
  have hd : ∀ t, 0 < t → HasDerivAt f (f' t) t := by
    intro t ht
    have h1 := (hasDerivAt_id t).mul ((Real.hasDerivAt_log ht.ne').sub_const (Real.log s))
    have h2 : HasDerivAt (fun t : ℝ => (t - s) ^ 2 / 2) ((t - s)) t := by
      have := (((hasDerivAt_id t).sub_const s).pow 2).div_const 2
      have e : (↑2 * (id t - s) ^ (2 - 1) * 1) / 2 = t - s := by simp
      exact (this.congr_deriv e)
    have := (h1.sub ((hasDerivAt_id t).sub_const s)).sub h2
    have e : 1 * (Real.log t - Real.log s) + id t * t⁻¹ - 1 - (t - s) = f' t := by
      simp only [f', id]; field_simp; ring
    exact (this : HasDerivAt f _ t).congr_deriv e
  have hd' : ∀ t, 0 < t → HasDerivAt f' (1 / t - 1) t := by
    intro t ht
    have := ((Real.hasDerivAt_log ht.ne').sub_const (Real.log s)).sub ((hasDerivAt_id t).sub_const s)
    have e : t⁻¹ - 1 = 1 / t - 1 := by rw [one_div]
    exact (this : HasDerivAt f' _ t).congr_deriv e
  have hfs : f s = 0 := by simp [f]
  have hf's : f' s = 0 := by simp [f']
  -- f' monotone on (0,1]
  have hmono' : MonotoneOn f' (Ioc 0 1) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ioc 0 1)
    · intro t ht; exact (hd' t ht.1).continuousAt.continuousWithinAt
    · intro t ht; rw [interior_Ioc] at ht
      exact (hd' t ht.1).differentiableAt.differentiableWithinAt
    · intro t ht; rw [interior_Ioc] at ht
      rw [(hd' t ht.1).deriv]
      have : 1 ≤ 1 / t := by rw [le_div_iff₀ ht.1]; linarith [ht.2]
      linarith
  suffices 0 ≤ f l by simp only [f] at this; linarith
  rcases le_total s l with h | h
  · -- f monotone on [s, l]
    have hm : MonotoneOn f (Icc s l) := by
      apply monotoneOn_of_deriv_nonneg (convex_Icc s l)
      · intro t ht; exact (hd t (lt_of_lt_of_le hs0 ht.1)).continuousAt.continuousWithinAt
      · intro t ht; rw [interior_Icc] at ht
        exact (hd t (lt_trans hs0 ht.1)).differentiableAt.differentiableWithinAt
      · intro t ht; rw [interior_Icc] at ht
        rw [(hd t (lt_trans hs0 ht.1)).deriv, ← hf's]
        exact hmono' ⟨hs0, hs1⟩ ⟨lt_trans hs0 ht.1, le_trans ht.2.le hl1⟩ ht.1.le
    have := hm ⟨le_rfl, h⟩ ⟨h, le_rfl⟩ h
    linarith
  · -- f antitone on [l, s]
    have hm : AntitoneOn f (Icc l s) := by
      apply antitoneOn_of_deriv_nonpos (convex_Icc l s)
      · intro t ht; exact (hd t (lt_of_lt_of_le hl0 ht.1)).continuousAt.continuousWithinAt
      · intro t ht; rw [interior_Icc] at ht
        exact (hd t (lt_trans hl0 ht.1)).differentiableAt.differentiableWithinAt
      · intro t ht; rw [interior_Icc] at ht
        rw [(hd t (lt_trans hl0 ht.1)).deriv, ← hf's]
        exact hmono' ⟨lt_trans hl0 ht.1, le_trans ht.2.le hs1⟩ ⟨hs0, hs1⟩ ht.2.le
    have := hm ⟨le_rfl, h⟩ ⟨h, le_rfl⟩ h
    linarith

variable {d : ℕ}

lemma coh_repr (X : Matrix (Fin d) (Fin d) ℂ) (hA : X.IsHermitian) :
    coherence X = ∑ i, ∑ x, ‖(hA.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℂ) x i‖ ^ 2 *
      hA.eigenvalues i * (Real.log (hA.eigenvalues i) - Real.log (X x x).re) := by
  set U : Matrix (Fin d) (Fin d) ℂ := (hA.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℂ)
  have hD : entropy (Matrix.diagonal (Matrix.diag X)) = -∑ x, (X x x).re * Real.log (X x x).re := by
    rw [diag_real hA, entropy_diag]
  unfold coherence
  rw [hD, entropy_spec hA]
  simp only [mul_sub, Finset.sum_sub_distrib]
  have e1 : ∑ i, ∑ x, ‖U x i‖ ^ 2 * hA.eigenvalues i * Real.log (hA.eigenvalues i) =
      ∑ i, hA.eigenvalues i * Real.log (hA.eigenvalues i) := by
    apply Finset.sum_congr rfl
    intro i _
    rw [← Finset.sum_mul, ← Finset.sum_mul, col_sum hA i, one_mul]
  have e2 : ∑ i, ∑ x, ‖U x i‖ ^ 2 * hA.eigenvalues i * Real.log (X x x).re =
      ∑ x, (X x x).re * Real.log (X x x).re := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro x _
    rw [← Finset.sum_mul, diag_re hA x]
  rw [e1, e2]
  ring

lemma var_eq (w l : Fin d → ℝ) (hw : ∑ i, w i = 1) :
    ∑ i, w i * (l i - ∑ j, w j * l j) ^ 2 = ∑ i, w i * l i ^ 2 - (∑ j, w j * l j) ^ 2 := by
  set m := ∑ j, w j * l j
  calc ∑ i, w i * (l i - m) ^ 2 = ∑ i, (w i * l i ^ 2 - 2 * m * (w i * l i) + m ^ 2 * w i) := by
        apply Finset.sum_congr rfl; intro i _; ring
    _ = ∑ i, w i * l i ^ 2 - 2 * m * m + m ^ 2 * ∑ i, w i := by
        rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    _ = _ := by rw [hw]; ring

lemma offdiag_eq (X : Matrix (Fin d) (Fin d) ℂ) (hA : X.IsHermitian) (x : Fin d) :
    ∑ y, (if x = y then 0 else ‖X x y‖ ^ 2) =
      ∑ i, ‖(hA.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℂ) x i‖ ^ 2 *
        (hA.eigenvalues i - (X x x).re) ^ 2 := by
  have hXX : ((X * X) x x).re = ∑ y, ‖X x y‖ ^ 2 := by
    rw [Matrix.mul_apply, Complex.re_sum]
    apply Finset.sum_congr rfl
    intro y _
    rw [← hA.apply y x, Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    exact Complex.ofReal_re _
  have hxx : ‖X x x‖ ^ 2 = (X x x).re ^ 2 := by
    have him : (X x x).im = 0 := by
      have h := congrArg Complex.im (hA.apply x x)
      simp at h; linarith
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, him]; ring
  have hsplit : ∀ y, (if x = y then (0:ℝ) else ‖X x y‖ ^ 2) =
      ‖X x y‖ ^ 2 - (if x = y then ‖X x y‖ ^ 2 else 0) := by
    intro y; split_ifs <;> simp
  have h1 : ∑ y, (if x = y then 0 else ‖X x y‖ ^ 2) = ((X * X) x x).re - (X x x).re ^ 2 := by
    rw [Finset.sum_congr rfl (fun y _ => hsplit y), Finset.sum_sub_distrib, Finset.sum_ite_eq,
      if_pos (Finset.mem_univ x), hXX, hxx]
  rw [h1, sq_diag_re hA x, diag_re hA x]
  have := var_eq (fun i => ‖(hA.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℂ) x i‖ ^ 2)
    hA.eigenvalues (row_sum hA x)
  rw [this]

/-- Hilbert–Schmidt Pinsker bound for the dephasing divergence -/
lemma hs_pinsker (X : Matrix (Fin d) (Fin d) ℂ) (hX : IsDensityMatrix X) :
    ∑ x, ∑ y, (if x = y then 0 else ‖X x y‖ ^ 2) ≤ 2 * coherence X := by
  have hA := hX.1.1
  rw [coh_repr X hA]
  simp only [offdiag_eq X hA]
  rw [Finset.sum_comm]
  set U : Matrix (Fin d) (Fin d) ℂ := (hA.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℂ)
  set lam := hA.eigenvalues
  have hlam : ∀ i, 0 ≤ lam i := hX.1.eigenvalues_nonneg
  have hsum : ∑ i, lam i = 1 := by
    have := hA.trace_eq_sum_eigenvalues
    rw [hX.2] at this
    have h2 := congrArg Complex.re this
    simpa using h2.symm
  have hlam1 : ∀ i, lam i ≤ 1 := fun i => by
    rw [← hsum]; exact Finset.single_le_sum (fun j _ => hlam j) (Finset.mem_univ i)
  have hσ0 : ∀ x, 0 ≤ (X x x).re := by
    intro x; have := hX.1.diag_nonneg (i := x); exact (Complex.nonneg_iff.mp this).1
  have hσsum : ∑ x, (X x x).re = 1 := by
    have h := congrArg Complex.re hX.2
    simpa [Matrix.trace, Complex.re_sum] using h
  have hσ1 : ∀ x, (X x x).re ≤ 1 := fun x => by
    rw [← hσsum]; exact Finset.single_le_sum (fun j _ => hσ0 j) (Finset.mem_univ x)
  have hzero : ∑ i, ∑ x, ‖U x i‖ ^ 2 * (lam i - (X x x).re) = 0 := by
    simp only [mul_sub, Finset.sum_sub_distrib]
    have e1 : ∑ i, ∑ x, ‖U x i‖ ^ 2 * lam i = 1 := by
      rw [← hsum]; apply Finset.sum_congr rfl; intro i _
      rw [← Finset.sum_mul, col_sum hA i, one_mul]
    have e2 : ∑ i, ∑ x, ‖U x i‖ ^ 2 * (X x x).re = 1 := by
      rw [Finset.sum_comm, ← hσsum]; apply Finset.sum_congr rfl; intro x _
      rw [← Finset.sum_mul, row_sum hA x, one_mul]
    rw [e1, e2, sub_self]
  -- termwise
  have hterm : ∀ i x, ‖U x i‖ ^ 2 * (lam i - (X x x).re) ^ 2 ≤
      2 * (‖U x i‖ ^ 2 * lam i * (Real.log (lam i) - Real.log (X x x).re)) -
        2 * (‖U x i‖ ^ 2 * (lam i - (X x x).re)) := by
    intro i x
    have hw : 0 ≤ ‖U x i‖ ^ 2 := sq_nonneg _
    rcases hw.eq_or_lt with hw0 | hwp
    · rw [← hw0]; simp
    rcases (hσ0 x).eq_or_lt with hs0 | hsp
    · -- σ = 0 forces λ = 0
      have hl0 : lam i = 0 := by
        have h1 := diag_re hA x
        rw [← hs0] at h1
        have h2 : ‖U x i‖ ^ 2 * lam i ≤ 0 := by
          rw [h1]
          exact Finset.single_le_sum (f := fun j => ‖U x j‖ ^ 2 * hA.eigenvalues j)
            (fun j _ => mul_nonneg (sq_nonneg _) (hlam j)) (Finset.mem_univ i)
        have := mul_nonneg hw (hlam i)
        have h3 : ‖U x i‖ ^ 2 * lam i = 0 := le_antisymm h2 this
        rcases mul_eq_zero.mp h3 with h | h
        · exact absurd h hwp.ne'
        · exact h
      rw [hl0, ← hs0]; simp
    rcases (hlam i).eq_or_lt with hl0 | hlp
    · rw [← hl0]
      have := hσ1 x
      simp
      nlinarith [mul_nonneg (mul_nonneg hw hsp.le) (show (0:ℝ) ≤ 2 - (X x x).re by linarith)]
    · have := kl_quad (lam i) (X x x).re hlp (hlam1 i) hsp (hσ1 x)
      have := mul_le_mul_of_nonneg_left this hw
      nlinarith
  calc ∑ i, ∑ x, ‖U x i‖ ^ 2 * (lam i - (X x x).re) ^ 2
      ≤ ∑ i, ∑ x, (2 * (‖U x i‖ ^ 2 * lam i * (Real.log (lam i) - Real.log (X x x).re)) -
        2 * (‖U x i‖ ^ 2 * (lam i - (X x x).re))) :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun x _ => hterm i x
    _ = 2 * ∑ i, ∑ x, ‖U x i‖ ^ 2 * lam i * (Real.log (lam i) - Real.log (X x x).re) -
        2 * ∑ i, ∑ x, ‖U x i‖ ^ 2 * (lam i - (X x x).re) := by
        simp only [Finset.sum_sub_distrib, Finset.mul_sum]
    _ = _ := by rw [hzero, mul_zero, sub_zero]

lemma coh_le_d (X : Matrix (Fin d) (Fin d) ℂ) (hX : IsDensityMatrix X) :
    coherence X ≤ d := by
  have hA := hX.1.1
  have hσ0 : ∀ x, 0 ≤ (X x x).re := by
    intro x; have := hX.1.diag_nonneg (i := x); exact (Complex.nonneg_iff.mp this).1
  have hσsum : ∑ x, (X x x).re = 1 := by
    have h := congrArg Complex.re hX.2
    simpa [Matrix.trace, Complex.re_sum] using h
  have hS := entropy_nonneg X hX.1 hX.2
  unfold coherence
  rw [diag_real hA, entropy_diag]
  have : ∀ x, -((X x x).re * Real.log (X x x).re) ≤ 1 := by
    intro x
    rcases (hσ0 x).eq_or_lt with h | h
    · rw [← h]; simp
    · have := Real.log_le_sub_one_of_pos (inv_pos.mpr h)
      rw [Real.log_inv] at this
      have := mul_le_mul_of_nonneg_left this h.le
      rw [mul_sub, mul_inv_cancel₀ h.ne'] at this
      nlinarith [hσ0 x]
  have := Finset.sum_le_sum (s := Finset.univ) fun x _ => this x
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one] at this
  rw [← Finset.sum_neg_distrib]
  linarith

end X6P41

open scoped Matrix ComplexConjugate ComplexOrder
open QAlgorithms QAlgorithms.Papers.Independent.Information100.P41

open X6P41 in
theorem solution {d : ℕ} (hd : 0 < d)
    (rho : Matrix (Fin d) (Fin d) ℂ) (hrho : IsDensityMatrix rho)
    (E : Superop (Fin d) (Fin d)) (hE : IsChannel E)
    (hfinal : ∀ x : Fin d, 0 < ((E rho) x x).re) :
    ‖anomaly E rho‖ ≤
      2 * Real.sqrt (coherence (E rho) * coheringPower E) / minPopulation (E rho) := by
  set R := E rho with hRdef
  set T := E (Matrix.diagonal (Matrix.diag rho)) with hTdef
  have hR := density_of_channel rho hrho E hE
  have hDrho : IsDensityMatrix (Matrix.diagonal (Matrix.diag rho)) := by
    refine ⟨Matrix.posSemidef_diagonal_iff.mpr (fun i => hrho.1.diag_nonneg), ?_⟩
    rw [Matrix.trace_diagonal]; exact hrho.2
  have hT := density_of_channel _ hDrho E hE
  have hinc : Matrix.diagonal (Matrix.diag (Matrix.diagonal (Matrix.diag rho))) =
      Matrix.diagonal (Matrix.diag rho) := by
    ext i j; simp [Matrix.diagonal_apply]
  -- coherence of T is bounded by the cohering power
  have hbdd : BddAbove {r : ℝ | ∃ omega : Matrix (Fin d) (Fin d) ℂ,
      IsDensityMatrix omega ∧ (Matrix.diagonal (Matrix.diag omega)) = omega ∧
        r = coherence (E omega)} := by
    refine ⟨d, ?_⟩
    rintro r ⟨omega, hom, -, rfl⟩
    exact coh_le_d _ (density_of_channel omega hom E hE)
  have hCT : coherence T ≤ coheringPower E :=
    le_csSup hbdd ⟨_, hDrho, hinc, rfl⟩
  -- minimal population
  set m := minPopulation R
  have hm_le : ∀ x, m ≤ (R x x).re := fun x =>
    csInf_le (Set.finite_range _).bddBelow ⟨x, rfl⟩
  have hm_pos : 0 < m := by
    have hne : (Set.range fun x : Fin d => (R x x).re).Nonempty := ⟨_, ⟨⟨0, hd⟩, rfl⟩⟩
    obtain ⟨x, hx⟩ := hne.csInf_mem (Set.finite_range _)
    simp only [m, minPopulation]
    rw [← hx]; exact hfinal x
  -- explicit anomaly
  have hRne : ∀ x, R x x ≠ 0 := fun x h => by
    have := hfinal x; rw [h] at this; simp at this
  have hinv : (Matrix.diagonal (Matrix.diag R))⁻¹ = Matrix.diagonal (fun x => (R x x)⁻¹) := by
    apply Matrix.inv_eq_left_inv
    rw [Matrix.diagonal_mul_diagonal]
    rw [← Matrix.diagonal_one]; congr 1; ext x
    simp [inv_mul_cancel₀ (hRne x)]
  have hanom : anomaly E rho = ∑ x, ∑ y, (R x x)⁻¹ *
      (if x = y then 0 else R x y) * T y x := by
    unfold anomaly outputAnomaly
    rw [← hRdef, ← hTdef, hinv, Matrix.trace]
    apply Finset.sum_congr rfl
    intro x _
    rw [Matrix.diag_apply, Matrix.mul_apply]
    apply Finset.sum_congr rfl
    intro y _
    rw [Matrix.diagonal_mul, Matrix.sub_apply, Matrix.diagonal_apply]
    by_cases h : x = y
    · subst h; simp
    · simp [h]
  -- off-diagonal real sequences
  set a : Fin d × Fin d → ℝ := fun p => if p.1 = p.2 then 0 else ‖R p.1 p.2‖
  set b : Fin d × Fin d → ℝ := fun p => if p.1 = p.2 then 0 else ‖T p.2 p.1‖
  have hbound : ‖anomaly E rho‖ ≤ (1 / m) * ∑ p, a p * b p := by
    rw [hanom, Fintype.sum_prod_type, Finset.mul_sum]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun x _ => ?_)
    rw [Finset.mul_sum]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun y _ => ?_)
    simp only [a, b]
    by_cases h : x = y
    · simp [h]
    · simp only [h, if_false, norm_mul, norm_inv]
      have hn : m ≤ ‖R x x‖ := (hm_le x).trans (Complex.re_le_norm _)
      have hinvle : ‖R x x‖⁻¹ ≤ 1 / m := by
        rw [one_div]; exact inv_anti₀ hm_pos hn
      have h0 : 0 ≤ ‖R x y‖ * ‖T y x‖ := by positivity
      calc ‖R x x‖⁻¹ * ‖R x y‖ * ‖T y x‖ = ‖R x x‖⁻¹ * (‖R x y‖ * ‖T y x‖) := by ring
        _ ≤ 1 / m * (‖R x y‖ * ‖T y x‖) := mul_le_mul_of_nonneg_right hinvle h0
  have hCS := Real.sum_mul_le_sqrt_mul_sqrt Finset.univ a b
  have ha2 : ∑ p, a p ^ 2 ≤ 2 * coherence R := by
    have := hs_pinsker R hR
    rw [Fintype.sum_prod_type]
    refine le_trans (le_of_eq ?_) this
    apply Finset.sum_congr rfl; intro x _; apply Finset.sum_congr rfl; intro y _
    simp only [a]; split_ifs <;> simp
  have hb2 : ∑ p, b p ^ 2 ≤ 2 * coherence T := by
    have := hs_pinsker T hT
    rw [Fintype.sum_prod_type, Finset.sum_comm]
    refine le_trans (le_of_eq ?_) this
    apply Finset.sum_congr rfl; intro y _; apply Finset.sum_congr rfl; intro x _
    simp only [b]
    by_cases h : x = y
    · subst h; simp
    · rw [if_neg h, if_neg (Ne.symm h)]
  have hCR0 : 0 ≤ coherence R := by
    have := hs_pinsker R hR
    have : 0 ≤ ∑ x, ∑ y, (if x = y then (0:ℝ) else ‖R x y‖ ^ 2) :=
      Finset.sum_nonneg fun x _ => Finset.sum_nonneg fun y _ => by split_ifs <;> positivity
    linarith
  have hCT0 : 0 ≤ coherence T := by
    have := hs_pinsker T hT
    have : 0 ≤ ∑ x, ∑ y, (if x = y then (0:ℝ) else ‖T x y‖ ^ 2) :=
      Finset.sum_nonneg fun x _ => Finset.sum_nonneg fun y _ => by split_ifs <;> positivity
    linarith
  have hCP0 : 0 ≤ coheringPower E := hCT0.trans hCT
  calc ‖anomaly E rho‖ ≤ (1 / m) * ∑ p, a p * b p := hbound
    _ ≤ (1 / m) * (Real.sqrt (∑ p, a p ^ 2) * Real.sqrt (∑ p, b p ^ 2)) :=
        mul_le_mul_of_nonneg_left hCS (by positivity)
    _ ≤ (1 / m) * (Real.sqrt (2 * coherence R) * Real.sqrt (2 * coheringPower E)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply mul_le_mul (Real.sqrt_le_sqrt ha2)
          (Real.sqrt_le_sqrt (hb2.trans (by linarith))) (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    _ = 2 * Real.sqrt (coherence R * coheringPower E) / m := by
        rw [← Real.sqrt_mul (by linarith), show 2 * coherence R * (2 * coheringPower E) =
          2 ^ 2 * (coherence R * coheringPower E) by ring, Real.sqrt_mul (by norm_num),
          Real.sqrt_sq (by norm_num)]
        ring
