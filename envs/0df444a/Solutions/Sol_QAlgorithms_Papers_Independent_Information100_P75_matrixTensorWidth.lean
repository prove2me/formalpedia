-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Information100.P75.matrixTensorWidth
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T10:30:08.260995+00:00
-- url     : https://prove2.me/submissions/74ee45f9-f539-4aef-afea-204edf3f4820

import Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P75_annihilatorObstruction
import Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P75_congruenceDiagonalization
noncomputable section

open scoped ComplexConjugate ComplexOrder Matrix

namespace X6P75K

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


/-! ### general tools for Lemma 14 -/

open scoped Kronecker

lemma single_psd (i : ι) : (Matrix.single i i (1 : ℂ)).PosSemidef := by
  have : Matrix.single i i (1 : ℂ) = Matrix.diagonal (Pi.single i 1) := by
    ext j k
    by_cases hj : j = k
    · subst hj; by_cases hi : i = j
      · subst hi; simp
      · simp [Matrix.single_apply, hi, Pi.single_apply, Ne.symm hi]
    · simp [Matrix.single_apply, hj, Matrix.diagonal_apply_ne _ hj]
      intro h1 h2; exact hj (h1 ▸ h2)
  rw [this]
  refine Matrix.PosSemidef.diagonal fun j => ?_
  by_cases hj : j = i
  · subst hj; simp
  · simp [Pi.single_apply, hj]

lemma exists_density [Nonempty ι] : ∃ D : Mat ι, QAlgorithms.IsDensityMatrix D := by
  obtain ⟨i⟩ := ‹Nonempty ι›
  exact ⟨Matrix.single i i 1, single_psd i, by simp⟩

lemma width_zero [Nonempty ι] : width (0 : Mat ι) = Real.pi := by
  unfold width
  rw [if_pos]
  obtain ⟨D, hD⟩ := exists_density (ι := ι)
  exact ⟨D, hD, by simp⟩

lemma width_nonneg [Nonempty ι] (X : Mat ι) : 0 ≤ width X := by
  by_cases h0 : X = 0
  · rw [h0, width_zero]; exact Real.pi_pos.le
  have := (annihilatorObstruction (0 : Mat ι)).1 X h0 (by simp)
  rw [width_zero, sub_self] at this
  unfold width
  split_ifs
  · exact Real.pi_pos.le
  · exact this

lemma width_of_not_mem (X : Mat ι) (h : (0 : ℂ) ∉ numericalRange X) :
    width X = Real.pi - gammaLength X := by
  unfold width; rw [if_neg h]

lemma phase_zero : phase 0 = 1 := by simp [phase]

lemma mem_omega_zero (R : Mat ι) :
    R ∈ omega (ι := ι) 0 ↔ QAlgorithms.IsDensityMatrix R := by
  constructor
  · rintro ⟨-, -, P, Q, hP, hQ, htr, rfl⟩
    simp only [blend, zero_div, neg_zero, phase_zero, one_smul]
    exact ⟨hP.add hQ, by rw [Matrix.trace_add]; exact htr⟩
  · rintro ⟨hR, htr⟩
    refine ⟨le_rfl, Real.pi_pos, R, 0, hR, Matrix.PosSemidef.zero, by simpa using htr, ?_⟩
    simp [blend, phase_zero]

lemma gl_pos [Nonempty ι] (X : Mat ι) (h : (0 : ℂ) ∉ numericalRange X) : 0 < gammaLength X := by
  by_contra hc
  have h0 : gammaLength X = 0 := le_antisymm (not_lt.1 hc) ENNReal.toReal_nonneg
  have hw : width X = Real.pi := by rw [width_of_not_mem X h, h0, sub_zero]
  obtain ⟨R, hR, hRX⟩ := (annihilatorObstruction X).2 (by rw [hw]; exact Real.pi_pos) 0
    (by rw [hw, sub_self]) Real.pi_pos
  exact h ⟨R, (mem_omega_zero R).1 hR, hRX⟩

lemma closedWidth_le (a : ℝ) (R : Mat ι) (hR : R ∈ omega (ι := ι) a) :
    closedWidth R ≤ a := by
  obtain ⟨ha, hap, P, Q, hP, hQ, -, rfl⟩ := hR
  have hsub : Set.Icc (-((Real.pi - a) / 2)) ((Real.pi - a) / 2) ⊆ A (blend a P Q) := by
    intro t ht
    rw [mem_A]
    intro v
    have hq : qf (blend a P Q) v = phase (a / 2) * qf P v + phase (-a / 2) * qf Q v := by
      simp only [qf, blend, Matrix.add_mulVec, Matrix.smul_mulVec, dotProduct_add,
        dotProduct_smul, smul_eq_mul]
    have hPr : (qf P v).im = 0 :=
      (Complex.nonneg_iff.mp ((Matrix.posSemidef_iff_dotProduct_mulVec.mp hP).2 v)).2.symm
    have hQr : (qf Q v).im = 0 :=
      (Complex.nonneg_iff.mp ((Matrix.posSemidef_iff_dotProduct_mulVec.mp hQ).2 v)).2.symm
    have hP0 : 0 ≤ (qf P v).re :=
      (Complex.nonneg_iff.mp ((Matrix.posSemidef_iff_dotProduct_mulVec.mp hP).2 v)).1
    have hQ0 : 0 ≤ (qf Q v).re :=
      (Complex.nonneg_iff.mp ((Matrix.posSemidef_iff_dotProduct_mulVec.mp hQ).2 v)).1
    rw [hq, mul_add, ← mul_assoc, ← mul_assoc, phase_mul, phase_mul, Complex.add_re,
      re_phase_mul, re_phase_mul, hPr, hQr]
    have h1 : 0 ≤ Real.cos (t + a / 2) := Real.cos_nonneg_of_mem_Icc
      ⟨by linarith [ht.1], by linarith [ht.2]⟩
    have h2 : 0 ≤ Real.cos (t + -a / 2) := Real.cos_nonneg_of_mem_Icc
      ⟨by linarith [ht.1], by linarith [ht.2]⟩
    nlinarith [mul_nonneg h1 hP0, mul_nonneg h2 hQ0]
  have hsub' : Set.Icc (-((Real.pi - a) / 2)) (-((Real.pi - a) / 2) + (Real.pi - a)) ⊆
      A (blend a P Q) := by
    rw [show -((Real.pi - a) / 2) + (Real.pi - a) = (Real.pi - a) / 2 by ring]; exact hsub
  have := gL_lower (blend a P Q) (-((Real.pi - a) / 2)) (Real.pi - a) (by linarith)
    (by linarith [Real.pi_pos]) hsub'
  unfold closedWidth; linarith

lemma omega_ne_zero (a : ℝ) (R : Mat ι) (hR : R ∈ omega (ι := ι) a) : R ≠ 0 := by
  obtain ⟨ha, hap, P, Q, hP, hQ, htr, rfl⟩ := hR
  intro h0
  have h := congrArg (fun M : Mat ι => (M.trace).re) h0
  simp only [blend, Matrix.trace_add, Matrix.trace_smul, smul_eq_mul, Complex.add_re,
    Complex.mul_re, Matrix.trace_zero, Complex.zero_re] at h
  have hPi : (P.trace).im = 0 := (Complex.nonneg_iff.mp hP.trace_nonneg).2.symm
  have hQi : (Q.trace).im = 0 := (Complex.nonneg_iff.mp hQ.trace_nonneg).2.symm
  have hre : (P.trace).re + (Q.trace).re = 1 := by
    have := congrArg Complex.re htr; simpa using this
  rw [hPi, hQi, re_phase, re_phase, neg_div, Real.cos_neg] at h
  have hc : 0 < Real.cos (a / 2) := Real.cos_pos_of_mem_Ioo
    ⟨by linarith [Real.pi_pos], by linarith⟩
  have : Real.cos (a / 2) * ((P.trace).re + (Q.trace).re) = 0 := by linarith
  rw [hre, mul_one] at this
  linarith

section Tensor

variable {κ : Type*} [Fintype κ] [DecidableEq κ]

omit [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] in
lemma kron_eq {ι' κ' : Type*} (A : Matrix ι' ι' ℂ) (B : Matrix κ' κ' ℂ) :
    Matrix.kronecker A B = A ⊗ₖ B := rfl

lemma trace_kron (A : Mat ι) (B : Mat κ) :
    (Matrix.kronecker A B).trace = A.trace * B.trace := by
  rw [kron_eq, Matrix.trace_kronecker]

lemma trace_kron_mul (A C : Mat ι) (B D : Mat κ) :
    (Matrix.kronecker A B * Matrix.kronecker C D).trace = (A * C).trace * (B * D).trace := by
  rw [kron_eq, kron_eq, ← Matrix.mul_kronecker_mul, Matrix.trace_kronecker]

lemma kron_density (D : Mat ι) (D' : Mat κ) (h : QAlgorithms.IsDensityMatrix D)
    (h' : QAlgorithms.IsDensityMatrix D') : QAlgorithms.IsDensityMatrix (Matrix.kronecker D D') :=
  ⟨h.1.kronecker h'.1, by rw [trace_kron, h.2, h'.2, one_mul]⟩

lemma zero_mem_kron_left [Nonempty κ] (X : Mat ι) (Y : Mat κ) (h : (0 : ℂ) ∈ numericalRange X) :
    (0 : ℂ) ∈ numericalRange (Matrix.kronecker X Y) := by
  obtain ⟨D, hD, hDX⟩ := h
  obtain ⟨D', hD'⟩ := exists_density (ι := κ)
  exact ⟨_, kron_density D D' hD hD', by rw [trace_kron_mul, hDX, zero_mul]⟩

lemma zero_mem_kron_right [Nonempty ι] (X : Mat ι) (Y : Mat κ) (h : (0 : ℂ) ∈ numericalRange Y) :
    (0 : ℂ) ∈ numericalRange (Matrix.kronecker X Y) := by
  obtain ⟨D', hD', hDY⟩ := h
  obtain ⟨D, hD⟩ := exists_density (ι := ι)
  exact ⟨_, kron_density D D' hD hD', by rw [trace_kron_mul, hDY, mul_zero]⟩

lemma psd_trace_re (P : Mat ι) (hP : P.PosSemidef) : P.trace = ((P.trace.re : ℝ) : ℂ) := by
  apply Complex.ext
  · simp
  · simp [(Complex.nonneg_iff.mp hP.trace_nonneg).2.symm]

/-- witness parts for a matrix whose numerical range avoids the origin -/
lemma witness [Nonempty ι] (X : Mat ι) (h0 : (0 : ℂ) ∉ numericalRange X) (hw : 0 < width X)
    (a : ℝ) (ha : Real.pi - width X ≤ a) (hap : a < Real.pi) :
    ∃ P Q : Mat ι, P.PosSemidef ∧ Q.PosSemidef ∧ P.trace + Q.trace = 1 ∧
      0 < P.trace.re ∧ 0 < Q.trace.re ∧ (Q * X).trace = -(phase a * (P * X).trace) := by
  obtain ⟨R, ⟨-, -, P, Q, hP, hQ, htr, rfl⟩, hRX⟩ := (annihilatorObstruction X).2 hw a ha hap
  have hrel : (Q * X).trace = -(phase a * (P * X).trace) := by
    simp only [blend, Matrix.add_mul, Matrix.smul_mul, Matrix.trace_add, Matrix.trace_smul,
      smul_eq_mul] at hRX
    have h1 : phase (a / 2) * phase (a / 2) = phase a := by rw [phase_mul]; ring_nf
    have h2 : phase (a / 2) * phase (-a / 2) = 1 := by
      rw [phase_mul, show a / 2 + -a / 2 = 0 by ring, phase_zero]
    linear_combination (phase (a / 2)) * hRX - (P * X).trace * h1 - (Q * X).trace * h2
  have hPr := psd_trace_re P hP
  have hQr := psd_trace_re Q hQ
  have hsum : P.trace.re + Q.trace.re = 1 := by
    have := congrArg Complex.re htr; simpa using this
  have hP0 : 0 ≤ P.trace.re := (Complex.nonneg_iff.mp hP.trace_nonneg).1
  have hQ0 : 0 ≤ Q.trace.re := (Complex.nonneg_iff.mp hQ.trace_nonneg).1
  refine ⟨P, Q, hP, hQ, htr, ?_, ?_, hrel⟩
  · rcases lt_or_eq_of_le hP0 with h | h
    · exact h
    exfalso
    have hP0' : P = 0 := (hP.trace_eq_zero_iff).1 (by rw [hPr, ← h]; simp)
    apply h0
    refine ⟨Q, ⟨hQ, by rw [hQr]; push_cast; rw [← h] at hsum; simp at hsum; rw [hsum]; simp⟩, ?_⟩
    rw [hrel, hP0', Matrix.zero_mul, Matrix.trace_zero, mul_zero, neg_zero]
  · rcases lt_or_eq_of_le hQ0 with h | h
    · exact h
    exfalso
    have hQ0' : Q = 0 := (hQ.trace_eq_zero_iff).1 (by rw [hQr, ← h]; simp)
    apply h0
    refine ⟨P, ⟨hP, by rw [hPr]; push_cast; rw [← h] at hsum; simp at hsum; rw [hsum]; simp⟩, ?_⟩
    have : (Q * X).trace = 0 := by rw [hQ0', Matrix.zero_mul, Matrix.trace_zero]
    rw [this] at hrel
    have hph : phase a ≠ 0 := by unfold phase; exact Complex.exp_ne_zero _
    have := neg_eq_zero.1 hrel.symm
    exact (mul_eq_zero.1 this).resolve_left hph

/-- the product annihilator of Theorem 3, normalized -/
lemma product_annihilator [Nonempty ι] [Nonempty κ] (X : Mat ι) (Y : Mat κ)
    (P Q : Mat ι) (R S : Mat κ) (a b : ℝ)
    (hP : P.PosSemidef) (hQ : Q.PosSemidef) (hPQ : P.trace + Q.trace = 1)
    (hP0 : 0 < P.trace.re) (hQ0 : 0 < Q.trace.re)
    (hrelX : (Q * X).trace = -(phase a * (P * X).trace))
    (hR : R.PosSemidef) (hS : S.PosSemidef) (hRS : R.trace + S.trace = 1)
    (hR0 : 0 < R.trace.re) (hS0 : 0 < S.trace.re)
    (hrelY : (S * Y).trace = -(phase b * (R * Y).trace))
    (hc0 : 0 ≤ a + b - Real.pi) (hcp : a + b - Real.pi < Real.pi) :
    ∃ Z ∈ omega (ι := ι × κ) (a + b - Real.pi), (Z * Matrix.kronecker X Y).trace = 0 := by
  set c := a + b - Real.pi
  set m : ℝ := P.trace.re * R.trace.re + Q.trace.re * S.trace.re
  have hm : 0 < m := by positivity
  set P' : Mat (ι × κ) := ((m⁻¹ : ℝ) : ℂ) • Matrix.kronecker P R
  set Q' : Mat (ι × κ) := ((m⁻¹ : ℝ) : ℂ) • Matrix.kronecker Q S
  have hm0 : (0 : ℂ) ≤ ((m⁻¹ : ℝ) : ℂ) := by exact_mod_cast (inv_pos.2 hm).le
  refine ⟨blend c P' Q', ⟨hc0, hcp, P', Q', (hP.kronecker hR).smul hm0,
    (hQ.kronecker hS).smul hm0, ?_, rfl⟩, ?_⟩
  · simp only [P', Q', Matrix.trace_smul, trace_kron, smul_eq_mul]
    rw [psd_trace_re P hP, psd_trace_re Q hQ, psd_trace_re R hR, psd_trace_re S hS]
    rw [← mul_add]
    push_cast
    have : (m : ℂ) = (P.trace.re : ℂ) * R.trace.re + Q.trace.re * S.trace.re := by
      simp only [m]; push_cast; ring
    rw [← this, inv_mul_cancel₀ (by exact_mod_cast hm.ne')]
  · simp only [blend, P', Q', Matrix.add_mul, Matrix.smul_mul, Matrix.trace_add,
      Matrix.trace_smul, smul_eq_mul, trace_kron_mul, hrelX, hrelY]
    have e : phase (-c / 2) * phase a * phase b = -phase (c / 2) := by
      rw [phase_mul, phase_mul, show -c / 2 + a + b = c / 2 + Real.pi by simp only [c]; ring,
        phase_add_pi]
    linear_combination (((m⁻¹ : ℝ) : ℂ) * ((P * X).trace * (R * Y).trace)) * e

end Tensor

/-! ### scalar arc components -/

lemma cos_nonneg_window (m : ℝ) (hm : -Real.pi ≤ m) (hm' : m < Real.pi) (h : 0 ≤ Real.cos m) :
    -(Real.pi / 2) ≤ m ∧ m ≤ Real.pi / 2 := by
  constructor
  · by_contra hc; push Not at hc
    have : Real.cos (-m) < 0 := Real.cos_neg_of_pi_div_two_lt_of_lt (by linarith) (by linarith)
    rw [Real.cos_neg] at this; linarith
  · by_contra hc; push Not at hc
    have : Real.cos m < 0 := Real.cos_neg_of_pi_div_two_lt_of_lt hc (by linarith)
    linarith

lemma comp (z : ℂ) (hz0 : z ≠ 0) (p q : ℝ) (hpq : p ≤ q) (hq : q - p ≤ Real.pi)
    (hz : ∀ s ∈ Set.Icc p q, 0 ≤ (phase s * z).re) :
    ∃ n : ℤ, -(Real.pi / 2) + n * (2 * Real.pi) ≤ p + Complex.arg z ∧
      q + Complex.arg z ≤ Real.pi / 2 + n * (2 * Real.pi) := by
  have hn0 : 0 < ‖z‖ := norm_pos_iff.2 hz0
  have hcos : ∀ s ∈ Set.Icc p q, 0 ≤ Real.cos (s + Complex.arg z) := by
    intro s hs
    have := hz s hs
    rw [re_phase_mul_polar] at this
    exact (mul_nonneg_iff_of_pos_left hn0).1 this
  set φ := Complex.arg z
  set m := (p + q) / 2 + φ
  set n : ℤ := ⌊(m + Real.pi) / (2 * Real.pi)⌋
  have h2pi : 0 < 2 * Real.pi := by positivity
  have hfl1 : (n : ℝ) ≤ (m + Real.pi) / (2 * Real.pi) := Int.floor_le _
  have hfl2 : (m + Real.pi) / (2 * Real.pi) < n + 1 := Int.lt_floor_add_one _
  rw [le_div_iff₀ h2pi] at hfl1
  rw [div_lt_iff₀ h2pi] at hfl2
  set m' := m - n * (2 * Real.pi)
  have hm'1 : -Real.pi ≤ m' := by simp only [m']; linarith
  have hm'2 : m' < Real.pi := by simp only [m']; linarith
  have hcm : 0 ≤ Real.cos m' := by
    simp only [m']; rw [Real.cos_sub_int_mul_two_pi]
    exact hcos _ ⟨by linarith, by linarith⟩
  obtain ⟨hl, hr⟩ := cos_nonneg_window m' hm'1 hm'2 hcm
  refine ⟨n, ?_, ?_⟩
  · by_contra hc; push Not at hc
    set y := p + φ - n * (2 * Real.pi)
    have hy1 : y < -(Real.pi / 2) := by simp only [y]; linarith
    have hy2 : -Real.pi - Real.pi / 2 < y := by
      have : y = m' - (q - p) / 2 := by simp only [y, m', m]; ring
      rw [this]; linarith
    have : Real.cos (-y) < 0 := Real.cos_neg_of_pi_div_two_lt_of_lt (by linarith) (by linarith)
    rw [Real.cos_neg] at this
    have h2 := hcos p ⟨le_rfl, hpq⟩
    rw [← Real.cos_sub_int_mul_two_pi _ n] at h2
    linarith
  · by_contra hc; push Not at hc
    set x := q + φ - n * (2 * Real.pi)
    have hx1 : Real.pi / 2 < x := by simp only [x]; linarith
    have hx2 : x < Real.pi + Real.pi / 2 := by
      have : x = m' + (q - p) / 2 := by simp only [x, m', m]; ring
      rw [this]; linarith
    have : Real.cos x < 0 := Real.cos_neg_of_pi_div_two_lt_of_lt hx1 hx2
    have h2 := hcos q ⟨hpq, le_rfl⟩
    rw [← Real.cos_sub_int_mul_two_pi _ n] at h2
    linarith

lemma re_phase_mul_prod (t : ℝ) (z z' : ℂ) :
    (phase t * (z * z')).re = ‖z‖ * ‖z'‖ * Real.cos (t + Complex.arg z + Complex.arg z') := by
  conv_lhs => rw [← Complex.norm_mul_exp_arg_mul_I z, ← Complex.norm_mul_exp_arg_mul_I z']
  have e1 : Complex.exp (↑(Complex.arg z) * Complex.I) = phase (Complex.arg z) := rfl
  have e2 : Complex.exp (↑(Complex.arg z') * Complex.I) = phase (Complex.arg z') := rfl
  rw [e1, e2]
  rw [show phase t * (↑‖z‖ * phase z.arg * (↑‖z'‖ * phase z'.arg)) =
    ((‖z‖ * ‖z'‖ : ℝ) : ℂ) * (phase t * phase z.arg * phase z'.arg) by push_cast; ring,
    phase_mul, phase_mul, Complex.re_ofReal_mul, re_phase]

lemma prod_scalar (z z' : ℂ) (p q p' q' : ℝ) (hpq : p ≤ q) (hq : q - p ≤ Real.pi)
    (hpq' : p' ≤ q') (hq' : q' - p' ≤ Real.pi)
    (hz : ∀ s ∈ Set.Icc p q, 0 ≤ (phase s * z).re)
    (hz' : ∀ s ∈ Set.Icc p' q', 0 ≤ (phase s * z').re) (t : ℝ)
    (ht1 : p + p' + Real.pi / 2 ≤ t) (ht2 : t ≤ q + q' - Real.pi / 2) :
    0 ≤ (phase t * (z * z')).re ∧
      (z ≠ 0 → z' ≠ 0 → p + p' + Real.pi / 2 < t → t < q + q' - Real.pi / 2 →
        0 < (phase t * (z * z')).re) := by
  by_cases h0 : z = 0
  · simp [h0]
  by_cases h0' : z' = 0
  · simp [h0']
  obtain ⟨n, hn1, hn2⟩ := comp z h0 p q hpq hq hz
  obtain ⟨n', hn1', hn2'⟩ := comp z' h0' p' q' hpq' hq' hz'
  rw [re_phase_mul_prod]
  have hpos : 0 < ‖z‖ * ‖z'‖ := mul_pos (norm_pos_iff.2 h0) (norm_pos_iff.2 h0')
  set θ := t + Complex.arg z + Complex.arg z' - ((n + n' : ℤ) : ℝ) * (2 * Real.pi)
  have hθ : Real.cos (t + Complex.arg z + Complex.arg z') = Real.cos θ := by
    simp only [θ]; rw [Real.cos_sub_int_mul_two_pi]
  rw [hθ]
  push_cast at θ
  constructor
  · exact mul_nonneg hpos.le (Real.cos_nonneg_of_mem_Icc ⟨by simp only [θ]; push_cast; linarith,
      by simp only [θ]; push_cast; linarith⟩)
  · intro _ _ hs1 hs2
    exact mul_pos hpos (Real.cos_pos_of_mem_Ioo ⟨by simp only [θ]; push_cast; linarith,
      by simp only [θ]; push_cast; linarith⟩)

section Tensor2

variable {κ : Type*} [Fintype κ] [DecidableEq κ]

lemma qf_kron (X : Mat ι) (Y : Mat κ) (x : ι → ℂ) (y : κ → ℂ) :
    qf (Matrix.kronecker X Y) (fun p => x p.1 * y p.2) = qf X x * qf Y y := by
  simp only [qf, dotProduct, Matrix.mulVec, kron_eq, Matrix.kroneckerMap_apply, Pi.star_apply,
    Fintype.sum_prod_type, Finset.sum_mul_sum, star_mul']
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_
  simp only [Finset.mul_sum, Finset.sum_mul]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => ?_
  ring

/-- product vectors bound the feasible set of a tensor product -/
lemma gl_kron_le_right (X : Mat ι) (Y : Mat κ) (hX : X ≠ 0) :
    gammaLength (Matrix.kronecker X Y) ≤ gammaLength Y := by
  obtain ⟨x0, hx0⟩ : ∃ x, qf X x ≠ 0 := by
    by_contra h; push Not at h; exact hX (eq_zero_of_qf X h)
  set z0 := qf X x0
  set φ0 := Complex.arg z0
  have hn : 0 < ‖z0‖ := norm_pos_iff.2 hx0
  have hsub : A (Matrix.kronecker X Y) ⊆ (fun t => t + φ0) ⁻¹' A Y := by
    intro t ht
    rw [Set.mem_preimage, mem_A]
    intro y
    have h := (mem_A _ t).1 ht (fun p => x0 p.1 * y p.2)
    rw [qf_kron, re_phase_mul_prod] at h
    rw [re_phase_mul_polar]
    rcases eq_or_ne (qf Y y) 0 with hy | hy
    · rw [hy]; simp
    have hpos : 0 < ‖z0‖ * ‖qf Y y‖ := mul_pos hn (norm_pos_iff.2 hy)
    have := (mul_nonneg_iff_of_pos_left hpos).1 h
    exact mul_nonneg (norm_nonneg _) (by simpa [φ0] using this)
  unfold gammaLength
  rw [gamma_shift _ 0, gamma_shift Y φ0]
  refine ENNReal.toReal_mono (A_vol_finite Y φ0) ?_
  calc volume (A (Matrix.kronecker X Y) ∩ Set.Ioc 0 (0 + 2 * Real.pi))
      ≤ volume ((fun t => t + φ0) ⁻¹' (A Y ∩ Set.Ioc φ0 (φ0 + 2 * Real.pi))) := by
        refine measure_mono fun t ht => ⟨hsub ht.1, ?_, ?_⟩
        · simp only; linarith [ht.2.1]
        · simp only; linarith [ht.2.2]
    _ = _ := measure_preimage_add_right _ _ _

end Tensor2

/-! ### congruence tools -/

omit [DecidableEq ι] in
lemma hR_congr {ι' : Type*} [Fintype ι'] (K : Matrix ι' ι ℂ) (M : Mat ι) (t : ℝ) :
    hermitianReal (phase t • (K * M * Kᴴ)) = K * hermitianReal (phase t • M) * Kᴴ := by
  unfold hermitianReal
  simp only [Matrix.conjTranspose_smul, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_add,
    Matrix.add_mul, Matrix.mul_assoc, smul_add]

lemma hR_diag (w : ι → ℂ) (t : ℝ) :
    hermitianReal (phase t • Matrix.diagonal w) =
      Matrix.diagonal (fun i => (((phase t * w i).re : ℝ) : ℂ)) := by
  unfold hermitianReal
  rw [← Matrix.diagonal_smul, Matrix.diagonal_conjTranspose, Matrix.diagonal_add,
    ← Matrix.diagonal_smul]
  congr 1
  funext i
  simp only [Pi.smul_apply, Pi.add_apply, Pi.star_apply, smul_eq_mul]
  rw [Complex.star_def, Complex.add_conj]
  push_cast; ring

lemma qf_congr (G D : Mat ι) (u : ι → ℂ) : qf (G * D * Gᴴ) u = qf D (Gᴴ *ᵥ u) := by
  simp only [qf]
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.star_mulVec,
    Matrix.conjTranspose_conjTranspose]

lemma diag_from (X G : Mat ι) (v : ι → ℂ) (hG : IsUnit G.det)
    (hX : X = G * Matrix.diagonal v * Gᴴ) :
    Matrix.diagonal v = G⁻¹ * X * (G⁻¹)ᴴ := by
  rw [hX]
  have h1 : G⁻¹ * G = 1 := Matrix.nonsing_inv_mul _ hG
  have h2 : Gᴴ * (G⁻¹)ᴴ = 1 := by
    rw [← Matrix.conjTranspose_mul, h1, Matrix.conjTranspose_one]
  calc Matrix.diagonal v = (G⁻¹ * G) * Matrix.diagonal v * (Gᴴ * (G⁻¹)ᴴ) := by
        rw [h1, h2, Matrix.one_mul, Matrix.mul_one]
    _ = _ := by simp only [Matrix.mul_assoc]

/-- from Lemma 10 and an arc of `X`: unit diagonal entries with controlled phases -/
lemma diag_data [Nonempty ι] (X : Mat ι) (h0 : (0 : ℂ) ∉ numericalRange X) :
    ∃ (G : Mat ι) (v : ι → ℂ) (p q : ℝ), IsUnit G.det ∧ X = G * Matrix.diagonal v * Gᴴ ∧
      (∀ j, v j ≠ 0) ∧ p < q ∧ q - p ≤ Real.pi ∧ gammaLength X ≤ q - p ∧
      ∀ j, ∀ s ∈ Set.Icc p q, 0 ≤ (phase s * v j).re := by
  have hX : X ≠ 0 := by rintro rfl; exact h0 (by
    obtain ⟨D, hD⟩ := exists_density (ι := ι); exact ⟨D, hD, by simp⟩)
  have hg := gl_pos X h0
  obtain ⟨G, v, hG, hXv, -⟩ := congruenceDiagonalization X hX (by unfold closedWidth; linarith)
  obtain ⟨p, q, hpq, hqp, hgl, hsub⟩ := (arc X hX).2 hg
  refine ⟨G, v, p, q, hG, hXv, ?_, hpq, hqp, hgl, ?_⟩
  · intro j hj
    apply h0
    set u : ι → ℂ := (G⁻¹)ᴴ *ᵥ Pi.single j 1
    have hu : Gᴴ *ᵥ u = Pi.single j 1 := by
      simp only [u, Matrix.mulVec_mulVec]
      rw [← Matrix.conjTranspose_mul, Matrix.nonsing_inv_mul _ hG, Matrix.conjTranspose_one,
        Matrix.one_mulVec]
    have hu0 : u ≠ 0 := by
      intro h; rw [h, Matrix.mulVec_zero] at hu
      have := congrFun hu j; simp at this
    refine ⟨dens u, dens_isDensity hu0, ?_⟩
    rw [dens_trace_mul, hXv, qf_congr, hu]
    simp [qf, dotProduct, Matrix.mulVec, Pi.single_apply, hj]
  · intro j s hs
    have hA := hsub hs
    have hD : (hermitianReal (phase s • Matrix.diagonal v)).PosSemidef := by
      rw [diag_from X G v hG hXv, hR_congr]
      exact hA.mul_mul_conjTranspose_same _
    rw [hR_diag] at hD
    have := hD.diag_nonneg (i := j)
    simp only [Matrix.diagonal_apply_eq] at this
    exact_mod_cast this

section Tensor3

variable {κ : Type*} [Fintype κ] [DecidableEq κ]

lemma upper_diag [Nonempty ι] [Nonempty κ] (X : Mat ι) (Y : Mat κ)
    (h0X : (0 : ℂ) ∉ numericalRange X) (h0Y : (0 : ℂ) ∉ numericalRange Y)
    (hsum : Real.pi < gammaLength X + gammaLength Y) :
    (0 : ℂ) ∉ numericalRange (Matrix.kronecker X Y) ∧
      gammaLength X + gammaLength Y - Real.pi ≤ gammaLength (Matrix.kronecker X Y) := by
  obtain ⟨G, v, p, q, hG, hXv, hv0, hpq, hqp, hglX, hv⟩ := diag_data X h0X
  obtain ⟨G', v', p', q', hG', hYv, hv0', hpq', hqp', hglY, hv'⟩ := diag_data Y h0Y
  set K := Matrix.kronecker G G'
  set w : ι × κ → ℂ := fun jk => v jk.1 * v' jk.2
  have hK : Matrix.kronecker X Y = K * Matrix.diagonal w * Kᴴ := by
    rw [hXv, hYv, kron_eq, Matrix.mul_kronecker_mul, Matrix.mul_kronecker_mul,
      Matrix.diagonal_kronecker_diagonal]
    simp only [K, w, kron_eq, Matrix.conjTranspose_kronecker]
  set L := (q - p) + (q' - p') - Real.pi
  have hL : 0 < L := by simp only [L]; linarith
  have hentry : ∀ t, p + p' + Real.pi / 2 ≤ t → t ≤ q + q' - Real.pi / 2 → ∀ i,
      0 ≤ (phase t * w i).re ∧ (p + p' + Real.pi / 2 < t → t < q + q' - Real.pi / 2 →
        0 < (phase t * w i).re) := by
    intro t ht1 ht2 i
    obtain ⟨h1, h2⟩ := prod_scalar (v i.1) (v' i.2) p q p' q' hpq.le hqp hpq'.le hqp'
      (hv i.1) (hv' i.2) t ht1 ht2
    exact ⟨h1, fun a b => h2 (hv0 i.1) (hv0' i.2) a b⟩
  have hsub : Set.Icc (p + p' + Real.pi / 2) (p + p' + Real.pi / 2 + L) ⊆
      A (Matrix.kronecker X Y) := by
    intro t ht
    have ht2 : t ≤ q + q' - Real.pi / 2 := by have := ht.2; simp only [L] at this; linarith
    show (hermitianReal (phase t • Matrix.kronecker X Y)).PosSemidef
    rw [hK, hR_congr, hR_diag]
    refine Matrix.PosSemidef.mul_mul_conjTranspose_same ?_ _
    refine Matrix.PosSemidef.diagonal fun i => ?_
    show (0 : ℂ) ≤ (((phase t * w i).re : ℝ) : ℂ)
    exact_mod_cast (hentry t ht.1 ht2 i).1
  have hLle : L ≤ gammaLength (Matrix.kronecker X Y) :=
    gL_lower _ _ L hL.le (by simp only [L]; linarith [Real.pi_pos]) hsub
  refine ⟨?_, by simp only [L] at hLle; linarith⟩
  -- the origin is not in the numerical range
  rintro ⟨R, ⟨hR, hRtr⟩, hRX⟩
  set t0 := p + p' + Real.pi / 2 + L / 2
  have ht01 : p + p' + Real.pi / 2 < t0 := by simp only [t0]; linarith
  have ht02 : t0 < q + q' - Real.pi / 2 := by simp only [t0, L]; linarith
  set R' := Kᴴ * R * K
  have hR' : R'.PosSemidef := hR.conjTranspose_mul_mul_same K
  have htr : (R' * Matrix.diagonal w).trace = 0 := by
    rw [← hRX, hK]
    simp only [R', Matrix.mul_assoc]
    rw [Matrix.trace_mul_comm]
    simp only [Matrix.mul_assoc]
  have hKu : IsUnit K.det := by
    simp only [K, kron_eq, Matrix.det_kronecker]
    exact (hG.pow _).mul (hG'.pow _)
  have hR'0 : R' ≠ 0 := by
    intro h0
    have hKi : (Kᴴ)⁻¹ * R' * K⁻¹ = R := by
      have h1 : (Kᴴ)⁻¹ * Kᴴ = 1 := Matrix.nonsing_inv_mul _ (by
        rw [Matrix.det_conjTranspose]; exact hKu.star)
      have h2 : K * K⁻¹ = 1 := Matrix.mul_nonsing_inv _ hKu
      simp only [R']
      calc (Kᴴ)⁻¹ * (Kᴴ * R * K) * K⁻¹ = ((Kᴴ)⁻¹ * Kᴴ) * R * (K * K⁻¹) := by
            simp only [Matrix.mul_assoc]
        _ = R := by rw [h1, h2, Matrix.one_mul, Matrix.mul_one]
    rw [h0, Matrix.mul_zero, Matrix.zero_mul] at hKi
    rw [← hKi, Matrix.trace_zero] at hRtr
    exact zero_ne_one hRtr
  have hdiag : ∀ i, (R' i i).im = 0 ∧ 0 ≤ (R' i i).re := fun i =>
    ⟨(Complex.nonneg_iff.mp (hR'.diag_nonneg (i := i))).2.symm,
      (Complex.nonneg_iff.mp (hR'.diag_nonneg (i := i))).1⟩
  obtain ⟨i0, hi0⟩ : ∃ i, 0 < (R' i i).re := by
    by_contra h; push Not at h
    apply hR'0
    apply (hR'.trace_eq_zero_iff).1
    rw [Matrix.trace]
    refine Finset.sum_eq_zero fun i _ => ?_
    apply Complex.ext
    · simp only [Matrix.diag, Complex.zero_re]; exact le_antisymm (h i) (hdiag i).2
    · simp only [Matrix.diag, Complex.zero_im]; exact (hdiag i).1
  have hre : (phase t0 * (R' * Matrix.diagonal w).trace).re =
      ∑ i, (R' i i).re * (phase t0 * w i).re := by
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_diagonal, Finset.mul_sum, Complex.re_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hri : R' i i = (((R' i i).re : ℝ) : ℂ) :=
      Complex.ext (by simp) (by simp [(hdiag i).1])
    rw [hri, show phase t0 * (((R' i i).re : ℂ) * w i) = ((R' i i).re : ℂ) * (phase t0 * w i)
      by ring, Complex.re_ofReal_mul, Complex.ofReal_re]
  have hpos : 0 < ∑ i, (R' i i).re * (phase t0 * w i).re := by
    refine lt_of_lt_of_le ?_ (Finset.single_le_sum (f := fun i => (R' i i).re * (phase t0 * w i).re)
      (fun i _ => mul_nonneg (hdiag i).2 (hentry t0 ht01.le ht02.le i).1) (Finset.mem_univ i0))
    exact mul_pos hi0 ((hentry t0 ht01.le ht02.le i0).2 ht01 ht02)
  rw [← hre, htr, mul_zero, Complex.zero_re] at hpos
  exact lt_irrefl _ hpos

end Tensor3

section Tensor4

variable {κ : Type*} [Fintype κ] [DecidableEq κ]

lemma gl_kron_le_left (X : Mat ι) (Y : Mat κ) (hY : Y ≠ 0) :
    gammaLength (Matrix.kronecker X Y) ≤ gammaLength X := by
  obtain ⟨y0, hy0⟩ : ∃ y, qf Y y ≠ 0 := by
    by_contra h; push Not at h; exact hY (eq_zero_of_qf Y h)
  set z0 := qf Y y0
  set φ0 := Complex.arg z0
  have hn : 0 < ‖z0‖ := norm_pos_iff.2 hy0
  have hsub : A (Matrix.kronecker X Y) ⊆ (fun t => t + φ0) ⁻¹' A X := by
    intro t ht
    rw [Set.mem_preimage, mem_A]
    intro x
    have h := (mem_A _ t).1 ht (fun p => x p.1 * y0 p.2)
    rw [qf_kron, mul_comm (qf X x) z0, re_phase_mul_prod] at h
    rw [re_phase_mul_polar]
    rcases eq_or_ne (qf X x) 0 with hx | hx
    · rw [hx]; simp
    have hpos : 0 < ‖z0‖ * ‖qf X x‖ := mul_pos hn (norm_pos_iff.2 hx)
    have := (mul_nonneg_iff_of_pos_left hpos).1 h
    exact mul_nonneg (norm_nonneg _) (by simpa [φ0] using this)
  unfold gammaLength
  rw [gamma_shift _ 0, gamma_shift X φ0]
  refine ENNReal.toReal_mono (A_vol_finite X φ0) ?_
  calc volume (A (Matrix.kronecker X Y) ∩ Set.Ioc 0 (0 + 2 * Real.pi))
      ≤ volume ((fun t => t + φ0) ⁻¹' (A X ∩ Set.Ioc φ0 (φ0 + 2 * Real.pi))) := by
        refine measure_mono fun t ht => ⟨hsub ht.1, ?_, ?_⟩
        · simp only; linarith [ht.2.1]
        · simp only; linarith [ht.2.2]
    _ = _ := measure_preimage_add_right _ _ _

lemma width_le_pi [Nonempty ι] (X : Mat ι) : width X ≤ Real.pi := by
  unfold width; split_ifs
  · exact le_rfl
  · have : 0 ≤ gammaLength X := ENNReal.toReal_nonneg
    linarith

lemma lower_sum [Nonempty ι] [Nonempty κ] (X : Mat ι) (Y : Mat κ)
    (h0X : (0 : ℂ) ∉ numericalRange X) (h0Y : (0 : ℂ) ∉ numericalRange Y)
    (hwX : 0 < width X) (hwY : 0 < width Y) (hsum : width X + width Y < Real.pi) :
    width X + width Y ≤ width (Matrix.kronecker X Y) := by
  obtain ⟨P, Q, hP, hQ, hPQ, hP0, hQ0, hrX⟩ :=
    witness X h0X hwX (Real.pi - width X) le_rfl (by linarith)
  obtain ⟨R, S, hR, hS, hRS, hR0, hS0, hrY⟩ :=
    witness Y h0Y hwY (Real.pi - width Y) le_rfl (by linarith)
  obtain ⟨Z, hZ, hZX⟩ := product_annihilator X Y P Q R S _ _ hP hQ hPQ hP0 hQ0 hrX hR hS hRS
    hR0 hS0 hrY (by linarith) (by linarith)
  have h1 := (annihilatorObstruction (Matrix.kronecker X Y)).1 Z (omega_ne_zero _ Z hZ) hZX
  have h2 := closedWidth_le _ Z hZ
  linarith

lemma zero_mem_ge [Nonempty ι] [Nonempty κ] (X : Mat ι) (Y : Mat κ)
    (h0X : (0 : ℂ) ∉ numericalRange X) (h0Y : (0 : ℂ) ∉ numericalRange Y)
    (hwX : 0 < width X) (hwY : 0 < width Y) (hsum : Real.pi ≤ width X + width Y) :
    (0 : ℂ) ∈ numericalRange (Matrix.kronecker X Y) := by
  set a := max (Real.pi - width X) (min (width Y) (Real.pi / 2))
  have ha1 : Real.pi - width X ≤ a := le_max_left _ _
  have hmin_pos : 0 < min (width Y) (Real.pi / 2) := lt_min hwY (by positivity)
  have ha0 : 0 < a := lt_of_lt_of_le hmin_pos (le_max_right _ _)
  have hap : a < Real.pi := max_lt (by linarith) (lt_of_le_of_lt (min_le_right _ _)
    (by linarith [Real.pi_pos]))
  have haY : a ≤ width Y := max_le (by linarith) (min_le_left _ _)
  obtain ⟨P, Q, hP, hQ, hPQ, hP0, hQ0, hrX⟩ := witness X h0X hwX a ha1 hap
  obtain ⟨R, S, hR, hS, hRS, hR0, hS0, hrY⟩ :=
    witness Y h0Y hwY (Real.pi - a) (by linarith) (by linarith)
  obtain ⟨Z, hZ, hZX⟩ := product_annihilator X Y P Q R S _ _ hP hQ hPQ hP0 hQ0 hrX hR hS hRS
    hR0 hS0 hrY (by linarith) (by linarith [Real.pi_pos])
  rw [show a + (Real.pi - a) - Real.pi = 0 by ring] at hZ
  exact ⟨Z, (mem_omega_zero Z).1 hZ, hZX⟩

theorem main [Nonempty ι] [Nonempty κ] (X : Mat ι) (Y : Mat κ) :
    width (Matrix.kronecker X Y) = min (width X + width Y) Real.pi := by
  by_cases hX0 : (0 : ℂ) ∈ numericalRange X
  · have h1 : width (Matrix.kronecker X Y) = Real.pi := by
      unfold width; rw [if_pos (zero_mem_kron_left X Y hX0)]
    have h2 : width X = Real.pi := by unfold width; rw [if_pos hX0]
    rw [h1, h2, min_eq_right (by linarith [width_nonneg Y])]
  by_cases hY0 : (0 : ℂ) ∈ numericalRange Y
  · have h1 : width (Matrix.kronecker X Y) = Real.pi := by
      unfold width; rw [if_pos (zero_mem_kron_right X Y hY0)]
    have h2 : width Y = Real.pi := by unfold width; rw [if_pos hY0]
    rw [h1, h2, min_eq_right (by linarith [width_nonneg X])]
  have hX : X ≠ 0 := by rintro rfl; exact hX0 (by
    obtain ⟨D, hD⟩ := exists_density (ι := ι); exact ⟨D, hD, by simp⟩)
  have hY : Y ≠ 0 := by rintro rfl; exact hY0 (by
    obtain ⟨D, hD⟩ := exists_density (ι := κ); exact ⟨D, hD, by simp⟩)
  have hwX := width_of_not_mem X hX0
  have hwY := width_of_not_mem Y hY0
  have hgX := gl_pos X hX0
  have hgY := gl_pos Y hY0
  have hgXle := (arc X hX).1
  have hgYle := (arc Y hY).1
  by_cases hs : width X + width Y < Real.pi
  · rw [min_eq_left hs.le]
    obtain ⟨h0, hgl⟩ := upper_diag X Y hX0 hY0 (by linarith)
    have hw := width_of_not_mem _ h0
    apply le_antisymm
    · linarith
    · rcases eq_or_lt_of_le (width_nonneg X) with hx | hx
      · have := gl_kron_le_right X Y hX
        linarith
      rcases eq_or_lt_of_le (width_nonneg Y) with hy | hy
      · have := gl_kron_le_left X Y hY
        linarith
      exact lower_sum X Y hX0 hY0 hx hy hs
  · push Not at hs
    rw [min_eq_right hs]
    have hx : 0 < width X := by linarith
    have hy : 0 < width Y := by linarith
    unfold width; rw [if_pos (zero_mem_ge X Y hX0 hY0 hx hy hs)]

end Tensor4

end X6P75K

open QAlgorithms.Papers.Independent.Information100.P75 in
theorem solution {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    [Fintype κ] [DecidableEq κ] [Nonempty κ] (X : Mat ι) (Y : Mat κ) :
    width (Matrix.kronecker X Y) = min (width X + width Y) Real.pi :=
  X6P75K.main X Y
