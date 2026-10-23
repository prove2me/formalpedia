-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Information100.P75.congruenceDiagonalization
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T10:10:34.63312+00:00
-- url     : https://prove2.me/submissions/72c6e2a0-3bda-4b81-b0f8-b5ce30b6e92d

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P75
noncomputable section

open scoped ComplexConjugate ComplexOrder Matrix

namespace X6P75D

open QAlgorithms.Papers.Independent.Information100.P75 MeasureTheory

/-! ### scalar trigonometry -/

lemma phase_eq (t : ℝ) : phase t = (Real.cos t : ℂ) + (Real.sin t : ℂ) * Complex.I := by
  unfold phase
  rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]

lemma re_phase_mul (t : ℝ) (z : ℂ) :
    (phase t * z).re = Real.cos t * z.re - Real.sin t * z.im := by
  rw [phase_eq]
  simp only [Complex.mul_re, Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, Complex.mul_im]
  ring

lemma phase_add_pi (t : ℝ) : phase (t + Real.pi) = - phase t := by
  rw [phase_eq, phase_eq, Real.cos_add_pi, Real.sin_add_pi]; push_cast; ring

/-- two-angle lemma -/
lemma eq_zero_of_two_angles (a b : ℝ) (z : ℂ) (hs : Real.sin (b - a) ≠ 0)
    (ha : (phase a * z).re = 0) (hb : (phase b * z).re = 0) : z = 0 := by
  rw [re_phase_mul] at ha hb
  rw [Real.sin_sub] at hs
  have h1 : z.re * (Real.sin b * Real.cos a - Real.cos b * Real.sin a) = 0 := by
    linear_combination (Real.sin b) * ha - (Real.sin a) * hb
  have h2 : z.im * (Real.sin b * Real.cos a - Real.cos b * Real.sin a) = 0 := by
    linear_combination (Real.cos b) * ha - (Real.cos a) * hb
  apply Complex.ext
  · simpa using (mul_eq_zero.1 h1).resolve_right hs
  · simpa using (mul_eq_zero.1 h2).resolve_right hs

/-- arc convexity at scalar level -/
lemma arc_convex (z : ℂ) (s1 s s2 : ℝ) (h1 : s1 ≤ s) (h2 : s ≤ s2) (hlt : s2 - s1 < Real.pi)
    (hz1 : 0 ≤ (phase s1 * z).re) (hz2 : 0 ≤ (phase s2 * z).re) : 0 ≤ (phase s * z).re := by
  rcases eq_or_lt_of_le (le_trans h1 h2) with heq | hlt'
  · have : s = s1 := le_antisymm (heq ▸ h2) h1
    rw [this]; exact hz1
  have hS : 0 < Real.sin (s2 - s1) := Real.sin_pos_of_pos_of_lt_pi (by linarith) hlt
  have hA : 0 ≤ Real.sin (s2 - s) := Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith)
  have hB : 0 ≤ Real.sin (s - s1) := Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith)
  have key : Real.sin (s2 - s1) * (phase s * z).re =
      Real.sin (s2 - s) * (phase s1 * z).re + Real.sin (s - s1) * (phase s2 * z).re := by
    simp only [re_phase_mul, Real.sin_sub]
    ring
  have : 0 ≤ Real.sin (s2 - s1) * (phase s * z).re := by
    rw [key]; positivity
  exact (mul_nonneg_iff_of_pos_left hS).1 this

/-! ### the angular feasibility set -/

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def qf (X : Mat ι) (v : ι → ℂ) : ℂ := star v ⬝ᵥ (X *ᵥ v)

lemma qf_conjTranspose (Z : Mat ι) (v : ι → ℂ) : star v ⬝ᵥ (Zᴴ *ᵥ v) = star (qf Z v) := by
  simp only [qf, dotProduct, Matrix.mulVec, Matrix.conjTranspose_apply, Pi.star_apply, star_sum,
    star_mul', star_star, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

lemma qf_smul (c : ℂ) (Z : Mat ι) (v : ι → ℂ) : star v ⬝ᵥ ((c • Z) *ᵥ v) = c * qf Z v := by
  rw [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul, qf]

lemma qf_hR (X : Mat ι) (t : ℝ) (v : ι → ℂ) :
    star v ⬝ᵥ (hermitianReal (phase t • X) *ᵥ v) = ((phase t * qf X v).re : ℂ) := by
  unfold hermitianReal
  rw [Matrix.smul_mulVec, dotProduct_smul, Matrix.add_mulVec, dotProduct_add,
    qf_conjTranspose, qf_smul, smul_eq_mul]
  have hq : qf (phase t • X) v = phase t * qf X v := qf_smul _ _ _
  have := Complex.add_conj (phase t * qf X v)
  rw [hq, Complex.star_def, this]
  push_cast; ring

lemma hR_herm (Z : Mat ι) : (hermitianReal Z).IsHermitian := by
  unfold hermitianReal Matrix.IsHermitian
  rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_add, Matrix.conjTranspose_conjTranspose,
    add_comm]
  congr 1
  simp

def A (X : Mat ι) : Set ℝ := {t | (hermitianReal (phase t • X)).PosSemidef}

lemma mem_A (X : Mat ι) (t : ℝ) : t ∈ A X ↔ ∀ v, 0 ≤ (phase t * qf X v).re := by
  simp only [A, Set.mem_setOf_eq, Matrix.posSemidef_iff_dotProduct_mulVec, qf_hR,
    Complex.zero_le_real]
  exact ⟨fun h => h.2, fun h => ⟨hR_herm _, h⟩⟩

lemma continuous_phase : Continuous phase := by
  unfold phase
  exact Complex.continuous_exp.comp (Complex.continuous_ofReal.mul continuous_const)

lemma A_closed (X : Mat ι) : IsClosed (A X) := by
  have : A X = ⋂ v : ι → ℂ, {t | 0 ≤ (phase t * qf X v).re} := by
    ext t; rw [mem_A]; simp
  rw [this]
  exact isClosed_iInter fun v => isClosed_le continuous_const
    (Complex.continuous_re.comp (continuous_phase.mul continuous_const))

lemma phase_periodic (t : ℝ) (n : ℤ) : phase (n * (2 * Real.pi) + t) = phase t := by
  unfold phase
  rw [show (((n * (2 * Real.pi) + t : ℝ)) : ℂ) * Complex.I =
      n * (2 * Real.pi * Complex.I) + t * Complex.I by push_cast; ring,
    Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, one_mul]

lemma gammaSet_eq (X : Mat ι) : gammaSet X = A X ∩ Set.Ico (-Real.pi) Real.pi := by
  ext t; simp only [gammaSet, A, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_Ico]; tauto

lemma gamma_shift (X : Mat ι) (c : ℝ) :
    volume (gammaSet X) = volume (A X ∩ Set.Ioc c (c + 2 * Real.pi)) := by
  have hT : (0 : ℝ) < 2 * Real.pi := by positivity
  rw [gammaSet_eq]
  have h1 : volume (A X ∩ Set.Ico (-Real.pi) Real.pi) =
      volume (A X ∩ Set.Ioc (-Real.pi) (-Real.pi + 2 * Real.pi)) := by
    rw [show -Real.pi + 2 * Real.pi = Real.pi by ring]
    exact measure_congr ((Filter.EventuallyEq.refl _ _).inter Ico_ae_eq_Ioc)
  rw [h1]
  refine IsAddFundamentalDomain.measure_set_eq (isAddFundamentalDomain_Ioc hT (-Real.pi))
    (isAddFundamentalDomain_Ioc hT c) (A_closed X).measurableSet ?_
  rintro ⟨g, hg⟩
  obtain ⟨n, rfl⟩ := AddSubgroup.mem_zmultiples_iff.1 hg
  ext x
  simp only [Set.mem_preimage, A, Set.mem_setOf_eq]
  change (hermitianReal (phase (n • (2 * Real.pi) + x) • X)).PosSemidef ↔ _
  rw [zsmul_eq_mul, phase_periodic]

lemma A_vol_finite (X : Mat ι) (c : ℝ) : volume (A X ∩ Set.Ioc c (c + 2 * Real.pi)) ≠ ⊤ :=
  ne_top_of_le_ne_top (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top)
    (measure_mono Set.inter_subset_right)

lemma gL_lower (X : Mat ι) (α L : ℝ) (hL0 : 0 ≤ L) (hL : L < 2 * Real.pi)
    (hsub : Set.Icc α (α + L) ⊆ A X) : L ≤ gammaLength X := by
  unfold gammaLength
  rw [gamma_shift X (α - (2 * Real.pi - L) / 2)]
  have hs : Set.Icc α (α + L) ⊆ A X ∩ Set.Ioc (α - (2 * Real.pi - L) / 2)
      (α - (2 * Real.pi - L) / 2 + 2 * Real.pi) := by
    intro t ht
    refine ⟨hsub ht, ?_, ?_⟩
    · linarith [ht.1]
    · linarith [ht.2, Real.pi_pos]
  have := measure_mono (μ := volume) hs
  rw [Real.volume_Icc, show α + L - α = L by ring] at this
  exact (ENNReal.ofReal_le_iff_le_toReal (A_vol_finite X _)).1 this

lemma arcA (X : Mat ι) (s1 s s2 : ℝ) (h1 : s1 ≤ s) (h2 : s ≤ s2) (hlt : s2 - s1 < Real.pi)
    (hs1 : s1 ∈ A X) (hs2 : s2 ∈ A X) : s ∈ A X := by
  rw [mem_A] at *
  exact fun v => arc_convex _ s1 s s2 h1 h2 hlt (hs1 v) (hs2 v)

/-! ### vectors, densities, polarization -/

def nrm (v : ι → ℂ) : ℝ := ∑ i, ‖v i‖ ^ 2

lemma nrm_nonneg (v : ι → ℂ) : 0 ≤ nrm v := Finset.sum_nonneg fun _ _ => sq_nonneg _

lemma nrm_pos {v : ι → ℂ} (hv : v ≠ 0) : 0 < nrm v := by
  obtain ⟨i, hi⟩ : ∃ i, v i ≠ 0 := by
    by_contra h; push Not at h; exact hv (funext h)
  exact lt_of_lt_of_le (by positivity) (Finset.single_le_sum (f := fun i => ‖v i‖ ^ 2)
    (fun _ _ => sq_nonneg _) (Finset.mem_univ i))

def dens (v : ι → ℂ) : Mat ι := (((nrm v)⁻¹ : ℝ) : ℂ) • Matrix.vecMulVec v (star v)

lemma dens_psd (v : ι → ℂ) : (dens v).PosSemidef := by
  unfold dens
  refine (Matrix.posSemidef_vecMulVec_self_star v).smul ?_
  exact_mod_cast inv_nonneg.2 (nrm_nonneg v)

lemma dens_trace {v : ι → ℂ} (hv : v ≠ 0) : (dens v).trace = 1 := by
  unfold dens
  rw [Matrix.trace_smul]
  have : (Matrix.vecMulVec v (star v)).trace = ((nrm v : ℝ) : ℂ) := by
    simp only [Matrix.trace, Matrix.diag, Matrix.vecMulVec_apply, Pi.star_apply, nrm]
    push_cast
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Complex.star_def, Complex.mul_conj']
  rw [this, smul_eq_mul, ← Complex.ofReal_mul, inv_mul_cancel₀ (nrm_pos hv).ne']
  simp

lemma dens_trace_mul (v : ι → ℂ) (X : Mat ι) :
    (dens v * X).trace = (((nrm v)⁻¹ : ℝ) : ℂ) * qf X v := by
  unfold dens qf
  rw [Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul]
  congr 1
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.vecMulVec_apply, dotProduct,
    Matrix.mulVec, Pi.star_apply, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

lemma dens_isDensity {v : ι → ℂ} (hv : v ≠ 0) : QAlgorithms.IsDensityMatrix (dens v) :=
  ⟨dens_psd v, dens_trace hv⟩

lemma qf_ne_zero_of_not_mem {X : Mat ι} (h0 : (0 : ℂ) ∉ numericalRange X) {v : ι → ℂ}
    (hv : v ≠ 0) : qf X v ≠ 0 := by
  intro hq
  apply h0
  refine ⟨dens v, dens_isDensity hv, ?_⟩
  rw [dens_trace_mul, hq, mul_zero]

def bf (Z : Mat ι) (u w : ι → ℂ) : ℂ := star u ⬝ᵥ (Z *ᵥ w)

lemma qf_add (Z : Mat ι) (u w : ι → ℂ) :
    qf Z (u + w) = qf Z u + qf Z w + bf Z u w + bf Z w u := by
  simp only [qf, bf, star_add, Matrix.mulVec_add, dotProduct_add, add_dotProduct]
  ring

lemma bf_smul_right (Z : Mat ι) (u w : ι → ℂ) (c : ℂ) : bf Z u (c • w) = c * bf Z u w := by
  simp only [bf, Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]

lemma bf_smul_left (Z : Mat ι) (u w : ι → ℂ) (c : ℂ) : bf Z (c • u) w = star c * bf Z u w := by
  simp only [bf, star_smul, smul_dotProduct, smul_eq_mul]

lemma qf_smul_vec (Z : Mat ι) (w : ι → ℂ) (c : ℂ) : qf Z (c • w) = star c * c * qf Z w := by
  simp only [qf, star_smul, Matrix.mulVec_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul]
  ring

lemma bf_single (Z : Mat ι) (i j : ι) : bf Z (Pi.single i 1) (Pi.single j 1) = Z i j := by
  simp [bf, dotProduct, Matrix.mulVec, Pi.single_apply]

lemma eq_zero_of_qf (Z : Mat ι) (h : ∀ v, qf Z v = 0) : Z = 0 := by
  ext i j
  have h1 := h (Pi.single i 1 + Pi.single j 1)
  have h2 := h (Pi.single i 1 + Complex.I • Pi.single j 1)
  rw [qf_add, h, h, bf_single, bf_single] at h1
  rw [qf_add, h, qf_smul_vec, h, bf_smul_right, bf_smul_left, bf_single, bf_single] at h2
  simp only [Complex.star_def, Complex.conj_I] at h2
  simp only [Matrix.zero_apply]
  linear_combination (1 / 2 : ℂ) * h1 - (Complex.I / 2) * h2 + ((Z i j - Z j i) / 2) * Complex.I_sq

lemma qf_bound (X : Mat ι) (v : ι → ℂ) :
    ‖qf X v‖ ≤ 2 * (∑ i, ∑ j, ‖X i j‖) * nrm v := by
  have hv : ∀ i, ‖v i‖ ^ 2 ≤ nrm v := fun i =>
    Finset.single_le_sum (f := fun i => ‖v i‖ ^ 2) (fun _ _ => sq_nonneg _) (Finset.mem_univ i)
  unfold qf
  simp only [dotProduct, Matrix.mulVec, Pi.star_apply, Finset.mul_sum, Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
  rw [norm_mul, norm_mul, norm_star]
  have := hv i; have := hv j
  nlinarith [sq_nonneg (‖v i‖ - ‖v j‖), norm_nonneg (v i), norm_nonneg (v j),
    norm_nonneg (X i j), mul_nonneg (norm_nonneg (X i j)) (sq_nonneg (‖v i‖ - ‖v j‖))]

/-! ### the arc lemma -/

lemma phase_mul (s t : ℝ) : phase s * phase t = phase (s + t) := by
  unfold phase; rw [← Complex.exp_add]; push_cast; ring_nf

lemma re_phase (s : ℝ) : (phase s).re = Real.cos s := by
  rw [phase_eq]
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
    Complex.ofReal_im]
  ring

lemma re_phase_mul_polar (t : ℝ) (z : ℂ) :
    (phase t * z).re = ‖z‖ * Real.cos (t + Complex.arg z) := by
  conv_lhs => rw [← Complex.norm_mul_exp_arg_mul_I z]
  have : Complex.exp (↑(Complex.arg z) * Complex.I) = phase (Complex.arg z) := rfl
  rw [this, mul_left_comm, phase_mul, Complex.re_ofReal_mul, re_phase]

lemma arc (Z : Mat ι) (hZ : Z ≠ 0) :
    gammaLength Z ≤ Real.pi ∧ (0 < gammaLength Z → ∃ p q : ℝ, p < q ∧ q - p ≤ Real.pi ∧
      gammaLength Z ≤ q - p ∧ Set.Icc p q ⊆ A Z) := by
  obtain ⟨v, hv⟩ : ∃ v, qf Z v ≠ 0 := by
    by_contra h; push Not at h; exact hZ (eq_zero_of_qf Z h)
  set z0 := qf Z v
  set c := -Complex.arg z0 - Real.pi / 2
  set w := c - Real.pi / 2
  have hz0 : 0 < ‖z0‖ := norm_pos_iff.2 hv
  -- feasible angles lie in the arc [c, c + π] inside the window (w, w + 2π]
  have hS : A Z ∩ Set.Ioc w (w + 2 * Real.pi) ⊆ Set.Icc c (c + Real.pi) := by
    rintro t ⟨htA, htw⟩
    have h0 := (mem_A Z t).1 htA v
    rw [re_phase_mul_polar] at h0
    have hcos : 0 ≤ Real.cos (t + Complex.arg z0) := (mul_nonneg_iff_of_pos_left hz0).1 h0
    by_contra hn
    rw [Set.mem_Icc, not_and_or, not_le, not_le] at hn
    rcases hn with hn | hn
    · -- t ∈ (w, c): angle in (-π, -π/2)
      have : Real.cos (t + Complex.arg z0) < 0 := by
        rw [← Real.cos_neg]
        exact Real.cos_neg_of_pi_div_two_lt_of_lt
          (by simp only [c, w] at htw hn ⊢; linarith [htw.1])
          (by simp only [c, w] at htw hn ⊢; linarith [htw.1, Real.pi_pos])
      linarith
    · -- t ∈ (c + π, w + 2π]: angle in (π/2, π]
      have : Real.cos (t + Complex.arg z0) < 0 := by
        apply Real.cos_neg_of_pi_div_two_lt_of_lt
        · simp only [c] at hn; linarith
        · simp only [c, w] at htw; linarith [htw.2, Real.pi_pos]
      linarith
  have hgl : gammaLength Z = (volume (A Z ∩ Set.Ioc w (w + 2 * Real.pi))).toReal := by
    unfold gammaLength; rw [gamma_shift Z w]
  have hvolle : volume (A Z ∩ Set.Ioc w (w + 2 * Real.pi)) ≤ ENNReal.ofReal Real.pi := by
    calc _ ≤ volume (Set.Icc c (c + Real.pi)) := measure_mono hS
      _ = _ := by rw [Real.volume_Icc]; ring_nf
  refine ⟨?_, ?_⟩
  · rw [hgl]; exact ENNReal.toReal_le_of_le_ofReal Real.pi_pos.le hvolle
  intro hpos
  set S' := A Z ∩ Set.Icc c (c + Real.pi)
  have hS'c : IsCompact S' := isCompact_Icc.inter_left (A_closed Z)
  have hsub : A Z ∩ Set.Ioc w (w + 2 * Real.pi) ⊆ S' := fun t ht => ⟨ht.1, hS ht⟩
  have hne : (A Z ∩ Set.Ioc w (w + 2 * Real.pi)).Nonempty := by
    by_contra h
    rw [Set.not_nonempty_iff_eq_empty] at h
    rw [hgl, h] at hpos; simp at hpos
  have hS'ne : S'.Nonempty := hne.mono hsub
  set p := sInf S'
  set q := sSup S'
  have hp : p ∈ S' := hS'c.sInf_mem hS'ne
  have hq : q ∈ S' := hS'c.sSup_mem hS'ne
  have hS'pq : S' ⊆ Set.Icc p q := fun t ht =>
    ⟨csInf_le hS'c.bddBelow ht, le_csSup hS'c.bddAbove ht⟩
  have hqp : q - p ≤ Real.pi := by linarith [hp.2.1, hq.2.2]
  have hglpq : gammaLength Z ≤ q - p := by
    rw [hgl]
    have := measure_mono (μ := volume) (hsub.trans hS'pq)
    rw [Real.volume_Icc] at this
    exact ENNReal.toReal_le_of_le_ofReal (sub_nonneg.2 (hS'pq hp).2) this
  have hpq : p < q := by linarith
  refine ⟨p, q, hpq, hqp, hglpq, ?_⟩
  rcases lt_or_eq_of_le hqp with hlt | heq
  · intro t ht; exact arcA Z p t q ht.1 ht.2 hlt hp.1 hq.1
  · -- full half-circle: need an interior point
    by_cases hint : ∃ m ∈ S', p < m ∧ m < q
    · obtain ⟨m, hm, hpm, hmq⟩ := hint
      intro t ht
      rcases le_total t m with htm | htm
      · exact arcA Z p t m ht.1 htm (by linarith) hp.1 hm.1
      · exact arcA Z m t q htm ht.2 (by linarith) hm.1 hq.1
    · exfalso
      push Not at hint
      have hsub2 : A Z ∩ Set.Ioc w (w + 2 * Real.pi) ⊆ {p, q} := by
        intro t ht
        have h1 := hS'pq (hsub ht)
        rcases eq_or_lt_of_le h1.1 with h | h
        · left; exact h.symm
        · right; exact le_antisymm h1.2 (hint t (hsub ht) h)
      have : volume (A Z ∩ Set.Ioc w (w + 2 * Real.pi)) = 0 :=
        measure_mono_null hsub2 (Set.Finite.measure_zero (by simp) _)
      rw [hgl, this] at hpos; simp at hpos


/-! ### Lemma 10: congruence diagonalization -/

lemma star_phase (s : ℝ) : star (phase s) = phase (-s) := by
  rw [phase_eq, phase_eq, Real.cos_neg, Real.sin_neg]
  apply Complex.ext <;> simp

lemma phase_sub_phase (θ : ℝ) :
    phase θ - phase (-θ) = 2 * Complex.I * ((Real.sin θ : ℝ) : ℂ) := by
  rw [phase_eq, phase_eq, Real.cos_neg, Real.sin_neg]; push_cast; ring

/-- reconstruction of `X` from two Hermitian parts -/
lemma reconstruct (X : Mat ι) (s1 s2 : ℝ) (hs : Real.sin (s1 - s2) ≠ 0) :
    X = (phase (-s2) / (Complex.I * Real.sin (s1 - s2))) • hermitianReal (phase s1 • X) +
      (-phase (-s1) / (Complex.I * Real.sin (s1 - s2))) • hermitianReal (phase s2 • X) := by
  unfold hermitianReal
  simp only [Matrix.conjTranspose_smul, star_phase, smul_add, smul_smul]
  have hI : Complex.I * (Real.sin (s1 - s2) : ℂ) ≠ 0 :=
    mul_ne_zero Complex.I_ne_zero (by exact_mod_cast hs)
  have e1 : phase (-s2) / (Complex.I * Real.sin (s1 - s2)) * (2⁻¹ * phase s1) +
      -phase (-s1) / (Complex.I * Real.sin (s1 - s2)) * (2⁻¹ * phase s2) = 1 := by
    rw [div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div, div_eq_one_iff_eq hI]
    have h := phase_sub_phase (s1 - s2)
    rw [show -(s1 - s2) = s2 - s1 by ring] at h
    have m1 : phase (-s2) * phase s1 = phase (s1 - s2) := by rw [phase_mul]; ring_nf
    have m2 : phase (-s1) * phase s2 = phase (s2 - s1) := by rw [phase_mul]; ring_nf
    linear_combination (2⁻¹ : ℂ) * m1 - (2⁻¹ : ℂ) * m2 + (2⁻¹ : ℂ) * h
  have e2 : phase (-s2) / (Complex.I * Real.sin (s1 - s2)) * (2⁻¹ * phase (-s1)) +
      -phase (-s1) / (Complex.I * Real.sin (s1 - s2)) * (2⁻¹ * phase (-s2)) = 0 := by
    ring
  have : ∀ (α β γ δ : ℂ) (M N : Mat ι), α • M + β • N + (γ • M + δ • N) =
      (α + γ) • M + (β + δ) • N := by
    intros; simp only [add_smul]; abel
  rw [this, e1, e2, one_smul, zero_smul, add_zero]

/-- unitary diagonalization of a Hermitian matrix, in plain matrix form -/
lemma herm_diag (A : Mat ι) (hA : A.IsHermitian) :
    ∃ U : Mat ι, Uᴴ * U = 1 ∧ U * Uᴴ = 1 ∧
      Uᴴ * A * U = Matrix.diagonal (fun j => ((hA.eigenvalues j : ℝ) : ℂ)) := by
  refine ⟨(hA.eigenvectorUnitary : Mat ι), ?_, ?_, ?_⟩
  · have := Matrix.mem_unitaryGroup_iff'.1 (hA.eigenvectorUnitary).2
    rwa [Matrix.star_eq_conjTranspose] at this
  · have := Matrix.mem_unitaryGroup_iff.1 (hA.eigenvectorUnitary).2
    rwa [Matrix.star_eq_conjTranspose] at this
  · have := hA.conjStarAlgAut_star_eigenvectorUnitary
    simp only [Unitary.conjStarAlgAut_apply, Unitary.coe_star, star_star] at this
    rw [← Matrix.star_eq_conjTranspose]
    exact this

/-- a PSD matrix with a zero diagonal entry has a zero row and column -/
lemma psd_row_zero (K : Mat ι) (hK : K.PosSemidef) (j : ι) (hj : K j j = 0) (k : ι) :
    K j k = 0 ∧ K k j = 0 := by
  open scoped MatrixOrder in
  have h0 : 0 ≤ K := Matrix.nonneg_iff_posSemidef.mpr hK
  open scoped MatrixOrder in
  have hB : (CFC.sqrt K).PosSemidef := Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg K)
  open scoped MatrixOrder in
  have hKB : K = (CFC.sqrt K)ᴴ * CFC.sqrt K := by
    rw [hB.isHermitian.eq, CFC.sqrt_mul_sqrt_self K h0]
  set B := CFC.sqrt K
  have hcol : ∀ l, B l j = 0 := by
    have hjj : ∑ l, ((‖B l j‖ ^ 2 : ℝ) : ℂ) = 0 := by
      rw [← hj, hKB]
      simp only [Matrix.mul_apply, Matrix.conjTranspose_apply]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [Complex.star_def, Complex.conj_mul']
      push_cast; ring
    have hjj' : ∑ l, ‖B l j‖ ^ 2 = 0 := by exact_mod_cast hjj
    intro l
    have := (Finset.sum_eq_zero_iff_of_nonneg (fun l _ => sq_nonneg ‖B l j‖)).1 hjj' l
      (Finset.mem_univ l)
    simpa using this
  constructor
  · rw [hKB]; simp [Matrix.mul_apply, Matrix.conjTranspose_apply, hcol]
  · rw [hKB]; simp [Matrix.mul_apply, Matrix.conjTranspose_apply, hcol]

lemma col_eq {M U : Mat ι} {c : ι → ℂ} (h : ∀ k, M *ᵥ (fun i => U i k) = c k • (fun i => U i k)) :
    M * U = U * Matrix.diagonal c := by
  ext i k
  have := congrFun (h k) i
  simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at this
  rw [Matrix.mul_apply, this, Matrix.mul_diagonal, mul_comm]

/-- simultaneous diagonalization by congruence of two PSD matrices -/
lemma simul (H1 H2 : Mat ι) (h1 : H1.PosSemidef) (h2 : H2.PosSemidef) :
    ∃ F : Mat ι, IsUnit F.det ∧ (∃ d1 : ι → ℂ, Fᴴ * H1 * F = Matrix.diagonal d1) ∧
      (∃ d2 : ι → ℂ, Fᴴ * H2 * F = Matrix.diagonal d2) := by
  set S := H1 + H2
  have hS : S.PosSemidef := h1.add h2
  obtain ⟨U1, hU1a, hU1b, hU1S⟩ := herm_diag S hS.isHermitian
  set σ := hS.isHermitian.eigenvalues
  have hσ : ∀ j, 0 ≤ σ j := hS.eigenvalues_nonneg
  set t : ι → ℝ := fun j => if 0 < σ j then (Real.sqrt (σ j))⁻¹ else 1
  have ht : ∀ j, 0 < t j := by
    intro j; simp only [t]; split_ifs with h
    · exact inv_pos.2 (Real.sqrt_pos.2 h)
    · exact one_pos
  set e : ι → ℂ := fun j => if 0 < σ j then 1 else 0
  set Dt : Mat ι := Matrix.diagonal (fun j => ((t j : ℝ) : ℂ))
  have hDt : Dtᴴ = Dt := by
    simp only [Dt, Matrix.diagonal_conjTranspose]
    congr 1; funext j; simp
  set T := U1 * Dt
  set E : Mat ι := Matrix.diagonal e
  have hTS : Tᴴ * S * T = E := by
    simp only [T, Matrix.conjTranspose_mul, hDt]
    rw [show Dt * U1ᴴ * S * (U1 * Dt) = Dt * (U1ᴴ * S * U1) * Dt by
      simp only [Matrix.mul_assoc], hU1S]
    simp only [Dt, E, Matrix.diagonal_mul_diagonal]
    congr 1; funext j
    simp only [e, t]
    split_ifs with h
    · have hs := Real.sq_sqrt (hσ j)
      have hs0 : Real.sqrt (σ j) ≠ 0 := (Real.sqrt_pos.2 h).ne'
      rw [← Complex.ofReal_mul, ← Complex.ofReal_mul]
      rw [show (Real.sqrt (σ j))⁻¹ * σ j * (Real.sqrt (σ j))⁻¹ = σ j / Real.sqrt (σ j) ^ 2 by
        rw [div_eq_mul_inv, ← inv_pow]; ring, hs, div_self (ne_of_gt h)]
      simp
    · have : σ j = 0 := le_antisymm (not_lt.1 h) (hσ j)
      simp [this]
  set K1 := Tᴴ * H1 * T
  set K2 := Tᴴ * H2 * T
  have hK1 : K1.PosSemidef := h1.conjTranspose_mul_mul_same T
  have hK2 : K2.PosSemidef := h2.conjTranspose_mul_mul_same T
  have hKsum : K1 + K2 = E := by
    rw [← hTS]; simp only [K1, K2, S, Matrix.mul_add, Matrix.add_mul]
  have he : ∀ j, e j = 0 ∨ e j = 1 := by
    intro j; simp only [e]; split_ifs <;> simp
  have hEE : E * E = E := by
    simp only [E, Matrix.diagonal_mul_diagonal]
    congr 1; funext j; rcases he j with h | h <;> simp [h]
  -- zero rows of K1 outside the support of E
  have hrow : ∀ j, e j = 0 → ∀ k, K1 j k = 0 ∧ K1 k j = 0 := by
    intro j hj k
    refine psd_row_zero K1 hK1 j ?_ k
    have hsum : K1 j j + K2 j j = 0 := by
      have := congrFun (congrFun hKsum j) j
      simp only [Matrix.add_apply, E, Matrix.diagonal_apply_eq, hj] at this
      exact this
    exact (add_eq_zero_iff_of_nonneg hK1.diag_nonneg hK2.diag_nonneg).1 hsum |>.1
  have hEK : E * K1 = K1 := by
    ext j k
    simp only [E, Matrix.diagonal_mul]
    rcases he j with h | h
    · rw [h, zero_mul, (hrow j h k).1]
    · rw [h, one_mul]
  have hKE : K1 * E = K1 := by
    ext j k
    simp only [E, Matrix.mul_diagonal]
    rcases he k with h | h
    · rw [h, mul_zero, (hrow k h j).2]
    · rw [h, mul_one]
  -- the auxiliary Hermitian matrix
  set B := K1 + (2 : ℂ) • (1 - E)
  have hEh : E.IsHermitian := by
    simp only [E, Matrix.IsHermitian, Matrix.diagonal_conjTranspose]
    congr 1; funext j; rcases he j with h | h <;> simp [h]
  have hB : B.IsHermitian := by
    refine hK1.isHermitian.add ?_
    simp only [Matrix.IsHermitian, Matrix.conjTranspose_smul, Matrix.conjTranspose_sub,
      Matrix.conjTranspose_one, hEh.eq]
    congr 1; simp
  obtain ⟨U2, hU2a, hU2b, hU2B⟩ := herm_diag B hB
  set μ : ι → ℂ := fun j => ((hB.eigenvalues j : ℝ) : ℂ)
  have hBU : B * U2 = U2 * Matrix.diagonal μ := by
    rw [← hU2B, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hU2b, Matrix.one_mul]
  have hcol : ∀ k, B *ᵥ (fun i => U2 i k) = μ k • (fun i => U2 i k) := by
    intro k; ext i
    have := congrFun (congrFun hBU i) k
    rw [Matrix.mul_diagonal, Matrix.mul_apply] at this
    simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul]
    rw [this, mul_comm]
  have hEB : E * B = K1 := by
    simp only [B, Matrix.mul_add, Matrix.mul_smul, Matrix.mul_sub, Matrix.mul_one, hEE, hEK,
      sub_self, smul_zero, add_zero]
  have h1EB : (1 - E) * B = (2 : ℂ) • (1 - E) := by
    simp only [B, Matrix.mul_add, Matrix.mul_smul, Matrix.sub_mul, Matrix.one_mul, hEK, sub_self,
      zero_add, Matrix.mul_sub, Matrix.mul_one, hEE, sub_zero]
  -- the norm argument
  have hkill : ∀ w : ι → ℂ, E *ᵥ w = w → K1 *ᵥ w = (2 : ℂ) • w → w = 0 := by
    intro w hEw hKw
    have hq2 : 0 ≤ star w ⬝ᵥ (K2 *ᵥ w) :=
      (Matrix.posSemidef_iff_dotProduct_mulVec.mp hK2).2 w
    have hsum : star w ⬝ᵥ (E *ᵥ w) = star w ⬝ᵥ (K1 *ᵥ w) + star w ⬝ᵥ (K2 *ᵥ w) := by
      rw [← hKsum, Matrix.add_mulVec, dotProduct_add]
    rw [hEw, hKw, dotProduct_smul, smul_eq_mul] at hsum
    have hn := dotProduct_star_self_nonneg w
    have : star w ⬝ᵥ w + star w ⬝ᵥ (K2 *ᵥ w) = 0 := by linear_combination -hsum
    exact dotProduct_star_self_eq_zero.1 ((add_eq_zero_iff_of_nonneg hn hq2).1 this).1
  set α : ι → ℂ := fun k => if μ k = 2 then 0 else μ k
  set β : ι → ℂ := fun k => if μ k = 2 then 0 else 1
  have hcolK : ∀ k, K1 *ᵥ (fun i => U2 i k) = α k • (fun i => U2 i k) ∧
      E *ᵥ (fun i => U2 i k) = β k • (fun i => U2 i k) := by
    intro k
    set u : ι → ℂ := fun i => U2 i k
    have hK1u : K1 *ᵥ u = μ k • (E *ᵥ u) := by
      rw [← hEB, ← Matrix.mulVec_mulVec, hcol, Matrix.mulVec_smul]
    have h1u : (2 : ℂ) • ((1 - E) *ᵥ u) = μ k • ((1 - E) *ᵥ u) := by
      rw [← Matrix.smul_mulVec, ← h1EB, ← Matrix.mulVec_mulVec, hcol, Matrix.mulVec_smul]
    have hdec : u = E *ᵥ u + (1 - E) *ᵥ u := by
      rw [Matrix.sub_mulVec, Matrix.one_mulVec]; abel
    by_cases hμ : μ k = 2
    · simp only [α, β, hμ, if_true, zero_smul]
      set w := E *ᵥ u
      have hEw : E *ᵥ w = w := by simp only [w]; rw [Matrix.mulVec_mulVec, hEE]
      have hKw : K1 *ᵥ w = (2 : ℂ) • w := by
        simp only [w]; rw [Matrix.mulVec_mulVec, hKE, hK1u, hμ]
      have hw0 := hkill w hEw hKw
      refine ⟨?_, hw0⟩
      rw [hK1u, hw0, smul_zero]
    · simp only [α, β, hμ, if_false, one_smul]
      have h0 : (1 - E) *ᵥ u = 0 := by
        have : ((2 : ℂ) - μ k) • ((1 - E) *ᵥ u) = 0 := by rw [sub_smul, h1u, sub_self]
        exact (smul_eq_zero.1 this).resolve_left (sub_ne_zero.2 (Ne.symm hμ))
      have hEu : E *ᵥ u = u := by
        conv_rhs => rw [hdec]
        rw [h0, add_zero]
      exact ⟨by rw [hK1u, hEu], hEu⟩
  have hK1U : K1 * U2 = U2 * Matrix.diagonal α := col_eq fun k => (hcolK k).1
  have hEU : E * U2 = U2 * Matrix.diagonal β := col_eq fun k => (hcolK k).2
  refine ⟨T * U2, ?_, ⟨α, ?_⟩, ⟨β - α, ?_⟩⟩
  · rw [Matrix.det_mul, Matrix.det_mul]
    refine ((Matrix.isUnit_det_of_right_inverse hU1b).mul ?_).mul
      (Matrix.isUnit_det_of_right_inverse hU2b)
    rw [Matrix.det_diagonal, isUnit_iff_ne_zero, Finset.prod_ne_zero_iff]
    intro j _
    exact_mod_cast (ht j).ne'
  · rw [Matrix.conjTranspose_mul, show U2ᴴ * Tᴴ * H1 * (T * U2) = U2ᴴ * K1 * U2 by
      simp only [K1, Matrix.mul_assoc], Matrix.mul_assoc, hK1U, ← Matrix.mul_assoc, hU2a,
      Matrix.one_mul]
  · have hK2E : K2 = E - K1 := by rw [← hKsum]; abel
    rw [Matrix.conjTranspose_mul, show U2ᴴ * Tᴴ * H2 * (T * U2) = U2ᴴ * K2 * U2 by
      simp only [K2, Matrix.mul_assoc], hK2E, Matrix.mul_sub, Matrix.sub_mul,
      Matrix.mul_assoc, Matrix.mul_assoc, hEU, hK1U, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
      hU2a, Matrix.one_mul, Matrix.one_mul, Matrix.diagonal_sub]
    rfl

/-- congruence with an invertible matrix can be undone -/
lemma undo (F H : Mat ι) (hF : IsUnit F.det) (d : ι → ℂ) (h : Fᴴ * H * F = Matrix.diagonal d) :
    H = (F⁻¹)ᴴ * Matrix.diagonal d * (F⁻¹)ᴴᴴ := by
  rw [← h, Matrix.conjTranspose_conjTranspose]
  have h1 : (F⁻¹)ᴴ * Fᴴ = 1 := by
    rw [← Matrix.conjTranspose_mul, Matrix.mul_nonsing_inv _ hF, Matrix.conjTranspose_one]
  have h2 : F * F⁻¹ = 1 := Matrix.mul_nonsing_inv _ hF
  calc H = ((F⁻¹)ᴴ * Fᴴ) * H * (F * F⁻¹) := by rw [h1, h2, Matrix.one_mul, Matrix.mul_one]
    _ = _ := by simp only [Matrix.mul_assoc]

theorem main [Nonempty ι] (X : Mat ι) (hX : X ≠ 0) (hw : closedWidth X < Real.pi) :
    ∃ (G : Mat ι) (v : ι → ℂ), IsUnit G.det ∧ X = G * Matrix.diagonal v * Gᴴ ∧
      ∀ j, ‖v j‖ = 0 ∨ ‖v j‖ = 1 := by
  have hpos : 0 < gammaLength X := by unfold closedWidth at hw; linarith
  obtain ⟨p, q, hpq, -, -, hsub⟩ := (arc X hX).2 hpos
  set δ := min (q - p) 1
  have hδ : 0 < δ := lt_min (by linarith) one_pos
  have hδ1 : δ ≤ 1 := min_le_right _ _
  have hδq : δ ≤ q - p := min_le_left _ _
  have hsin : Real.sin (p - (p + δ)) ≠ 0 := by
    rw [show p - (p + δ) = -δ by ring, Real.sin_neg, neg_ne_zero]
    exact (Real.sin_pos_of_pos_of_lt_pi hδ (by linarith [Real.pi_gt_three])).ne'
  have hH1 : (hermitianReal (phase p • X)).PosSemidef := hsub ⟨le_rfl, hpq.le⟩
  have hH2 : (hermitianReal (phase (p + δ) • X)).PosSemidef := hsub ⟨by linarith, by linarith⟩
  obtain ⟨F, hF, ⟨d1, hd1⟩, ⟨d2, hd2⟩⟩ := simul _ _ hH1 hH2
  set c1 := phase (-(p + δ)) / (Complex.I * Real.sin (p - (p + δ)))
  set c2 := -phase (-p) / (Complex.I * Real.sin (p - (p + δ)))
  set G0 := (F⁻¹)ᴴ
  set w : ι → ℂ := c1 • d1 + c2 • d2
  have hXw : X = G0 * Matrix.diagonal w * G0ᴴ := by
    conv_lhs => rw [reconstruct X p (p + δ) hsin, undo F _ hF d1 hd1, undo F _ hF d2 hd2]
    have hd : Matrix.diagonal w = c1 • Matrix.diagonal d1 + c2 • Matrix.diagonal d2 := by
      ext i j; by_cases h : i = j
      · subst h; simp [w]
      · simp [w, Matrix.diagonal_apply_ne _ h]
    rw [hd]
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul]
    rfl
  have hG0 : IsUnit G0.det := by
    simp only [G0, Matrix.det_conjTranspose]
    exact (Matrix.isUnit_nonsing_inv_det F hF).star
  -- rescale to unimodular or zero entries
  set m : ι → ℝ := fun j => if w j = 0 then 1 else Real.sqrt ‖w j‖
  set v : ι → ℂ := fun j => if w j = 0 then 0 else w j / (‖w j‖ : ℂ)
  have hm : ∀ j, 0 < m j := by
    intro j; simp only [m]; split_ifs with h
    · exact one_pos
    · exact Real.sqrt_pos.2 (norm_pos_iff.2 h)
  set Dm : Mat ι := Matrix.diagonal (fun j => ((m j : ℝ) : ℂ))
  refine ⟨G0 * Dm, v, ?_, ?_, ?_⟩
  · rw [Matrix.det_mul]
    refine hG0.mul ?_
    rw [Matrix.det_diagonal, isUnit_iff_ne_zero, Finset.prod_ne_zero_iff]
    intro j _; exact_mod_cast (hm j).ne'
  · rw [hXw, Matrix.conjTranspose_mul]
    have hDm : Dmᴴ = Dm := by
      simp only [Dm, Matrix.diagonal_conjTranspose]; congr 1; funext j; simp
    rw [hDm, show G0 * Dm * Matrix.diagonal v * (Dm * G0ᴴ) =
      G0 * (Dm * Matrix.diagonal v * Dm) * G0ᴴ by simp only [Matrix.mul_assoc]]
    congr 2
    simp only [Dm, Matrix.diagonal_mul_diagonal]
    congr 1; funext j
    simp only [m, v]
    split_ifs with h
    · rw [h]; ring
    · have hn : (0 : ℝ) < ‖w j‖ := norm_pos_iff.2 h
      have hs := Real.mul_self_sqrt hn.le
      have hn' : ((‖w j‖ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
      field_simp
      rw [← Complex.ofReal_pow, Real.sq_sqrt (norm_nonneg _)]
  · intro j
    simp only [v]
    split_ifs with h
    · left; simp
    · right
      rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_norm, div_self (norm_ne_zero_iff.2 h)]

end X6P75D

open QAlgorithms.Papers.Independent.Information100.P75 in
theorem solution {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (X : Mat ι) (hX : X ≠ 0) (hw : closedWidth X < Real.pi) :
    ∃ (G : Mat ι) (v : ι → ℂ), IsUnit G.det ∧ X = G * Matrix.diagonal v * Gᴴ ∧
      ∀ j, ‖v j‖ = 0 ∨ ‖v j‖ = 1 :=
  X6P75D.main X hX hw
