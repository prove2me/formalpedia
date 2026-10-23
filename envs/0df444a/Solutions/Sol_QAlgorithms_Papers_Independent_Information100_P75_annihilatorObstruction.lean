-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Information100.P75.annihilatorObstruction
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T09:51:23.415465+00:00
-- url     : https://prove2.me/submissions/6c03371a-5e5c-4faf-95ca-48cc52ed9b2d

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P75
noncomputable section

open scoped ComplexConjugate ComplexOrder Matrix

namespace X6P75L

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

/-! ### part (i): the obstruction -/

lemma star_phase (s : ℝ) : star (phase s) = phase (-s) := by
  rw [phase_eq, phase_eq, Real.cos_neg, Real.sin_neg]
  apply Complex.ext <;> simp

lemma trace_identity (X Y : Mat ι) (hYX : (Y * X).trace = 0) (t s : ℝ) :
    (hermitianReal (phase t • Y) * hermitianReal (phase s • X)).trace =
      (((phase (t - s) * (Y * Xᴴ).trace).re / 2 : ℝ) : ℂ) := by
  unfold hermitianReal
  simp only [Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, Matrix.add_mul,
    Matrix.mul_add, Matrix.trace_smul, Matrix.trace_add, smul_eq_mul]
  have h1 : (Yᴴ * Xᴴ).trace = 0 := by
    rw [← Matrix.conjTranspose_mul, Matrix.trace_conjTranspose, Matrix.trace_mul_comm, hYX,
      star_zero]
  have h2 : (Yᴴ * X).trace = star ((Y * Xᴴ).trace) := by
    rw [← Matrix.trace_conjTranspose, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
      Matrix.trace_mul_comm]
  rw [hYX, h1, h2, star_phase, star_phase]
  set β := (Y * Xᴴ).trace
  have hw : phase t * phase (-s) * β + star (phase t * phase (-s) * β) =
      ((2 * (phase (t - s) * β).re : ℝ) : ℂ) := by
    rw [Complex.star_def, Complex.add_conj, phase_mul, ← sub_eq_add_neg]
  have hst : star (phase t * phase (-s) * β) = phase (-t) * phase s * star β := by
    rw [star_mul', star_mul', star_phase, star_phase, neg_neg]
  rw [hst] at hw
  push_cast at hw ⊢
  linear_combination (1 / 4 : ℂ) * hw

/-- the trace of a PSD matrix against `H` as a sum of quadratic forms -/
lemma psd_trace_qf (P : Mat ι) (hP : P.PosSemidef) :
    ∃ w : ι → ι → ℂ, (∀ H : Mat ι, (P * H).trace = ∑ k, qf H (w k)) ∧
      ((∀ k, w k = 0) → P = 0) := by
  open scoped MatrixOrder in
  have h0 : 0 ≤ P := Matrix.nonneg_iff_posSemidef.mpr hP
  open scoped MatrixOrder in
  have hB : (CFC.sqrt P).PosSemidef := Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg P)
  open scoped MatrixOrder in
  have hPB : P = (CFC.sqrt P)ᴴ * CFC.sqrt P := by
    rw [hB.isHermitian.eq, CFC.sqrt_mul_sqrt_self P h0]
  set B := CFC.sqrt P
  refine ⟨fun k j => star (B k j), fun H => ?_, fun hw => ?_⟩
  · rw [hPB, Matrix.mul_assoc, Matrix.trace_mul_comm]
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply, qf,
      dotProduct, Matrix.mulVec, star_star, Finset.sum_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [Pi.star_apply, star_star]
    ring
  · have : B = 0 := by
      ext k j
      have := congrFun (hw k) j
      simpa using this
    rw [hPB, this]; simp

lemma qf_psd_re_nonneg (H : Mat ι) (hH : H.PosSemidef) (w : ι → ℂ) : 0 ≤ (qf H w).re :=
  (Complex.nonneg_iff.mp ((Matrix.posSemidef_iff_dotProduct_mulVec.mp hH).2 w)).1

lemma interior_pos (X : Mat ι) (h0 : (0 : ℂ) ∉ numericalRange X) (p q s : ℝ)
    (hsub : Set.Icc p q ⊆ A X) (hps : p < s) (hsq : s < q) (w : ι → ℂ) (hw : w ≠ 0) :
    0 < (phase s * qf X w).re := by
  have hz := qf_ne_zero_of_not_mem h0 hw
  set z := qf X w
  set η := min (min (s - p) (q - s)) 1
  have hη : 0 < η := lt_min (lt_min (by linarith) (by linarith)) one_pos
  have hη1 : η ≤ 1 := min_le_right _ _
  have hηa : η ≤ s - p := (min_le_left _ _).trans (min_le_left _ _)
  have hηb : η ≤ q - s := (min_le_left _ _).trans (min_le_right _ _)
  have hs := (mem_A X s).1 (hsub ⟨hps.le, hsq.le⟩) w
  have hplus := (mem_A X (s + η)).1 (hsub ⟨by linarith, by linarith⟩) w
  have hminus := (mem_A X (s - η)).1 (hsub ⟨by linarith, by linarith⟩) w
  rcases lt_or_eq_of_le hs with h | h
  · exact h
  exfalso
  have hsum : (phase (s + η) * z).re + (phase (s - η) * z).re =
      2 * Real.cos η * (phase s * z).re := by
    simp only [re_phase_mul, Real.cos_add, Real.cos_sub, Real.sin_add, Real.sin_sub]
    ring
  have hp0 : (phase (s + η) * z).re = 0 := by
    rw [← h, mul_zero] at hsum; linarith
  apply hz
  refine eq_zero_of_two_angles s (s + η) z ?_ h.symm hp0
  rw [add_sub_cancel_left]
  exact (Real.sin_pos_of_pos_of_lt_pi hη (by linarith [Real.pi_gt_three])).ne'

lemma hR_zero_iff (Y : Mat ι) (t : ℝ) (h : hermitianReal (phase t • Y) = 0) (v : ι → ℂ) :
    (phase t * qf Y v).re = 0 := by
  have := qf_hR Y t v
  rw [h, Matrix.zero_mulVec, dotProduct_zero] at this
  exact_mod_cast this.symm

lemma zero_mem_numericalRange_zero [Nonempty ι] : (0 : ℂ) ∈ numericalRange (0 : Mat ι) := by
  obtain ⟨i⟩ := ‹Nonempty ι›
  have hv : (Pi.single i (1 : ℂ) : ι → ℂ) ≠ 0 := by
    intro h; have := congrFun h i; simp at this
  exact ⟨dens _, dens_isDensity hv, by simp⟩

theorem part1 [Nonempty ι] (X : Mat ι) (Y : Mat ι) (hY : Y ≠ 0) (hYX : (Y * X).trace = 0) :
    Real.pi - width X ≤ closedWidth Y := by
  unfold width closedWidth
  split_ifs with h0
  · linarith [(arc Y hY).1]
  have hX : X ≠ 0 := by rintro rfl; exact h0 zero_mem_numericalRange_zero
  by_contra hc
  have hsum : Real.pi < gammaLength X + gammaLength Y := by linarith
  obtain ⟨hXle, hXarc⟩ := arc X hX
  obtain ⟨hYle, hYarc⟩ := arc Y hY
  have hgX : 0 < gammaLength X := by linarith
  have hgY : 0 < gammaLength Y := by linarith
  obtain ⟨p', q', hpq', -, hlenX, hsubX⟩ := hXarc hgX
  obtain ⟨p, q, hpq, -, hlenY, hsubY⟩ := hYarc hgY
  set β := (Y * Xᴴ).trace
  -- nonnegativity of the pairing on the difference interval
  have hpair : ∀ t ∈ Set.Icc p q, ∀ s ∈ Set.Icc p' q',
      0 ≤ ((hermitianReal (phase t • Y) * hermitianReal (phase s • X)).trace).re := by
    intro t ht s hs
    obtain ⟨w, hw, -⟩ := psd_trace_qf _ (hsubY ht)
    rw [hw, Complex.re_sum]
    exact Finset.sum_nonneg fun k _ => qf_psd_re_nonneg _ (hsubX hs) _
  have hG : ∀ d, p - q' ≤ d → d ≤ q - p' → 0 ≤ (phase d * β).re := by
    intro d hd1 hd2
    set t := max p (d + p')
    have ht : t ∈ Set.Icc p q := ⟨le_max_left _ _, max_le hpq.le (by linarith)⟩
    have hs : t - d ∈ Set.Icc p' q' := by
      refine ⟨by have := le_max_right p (d + p'); linarith, ?_⟩
      have : t ≤ q' + d := max_le (by linarith) (by linarith)
      linarith
    have := hpair t ht (t - d) hs
    rw [trace_identity X Y hYX, sub_sub_cancel, Complex.ofReal_re] at this
    linarith
  set L := (q - p) + (q' - p') - Real.pi
  have hL : 0 < L := by simp only [L]; linarith
  set δ := min L 1
  have hδ : 0 < δ := lt_min hL one_pos
  have hδL : δ ≤ L := min_le_left _ _
  have hδ1 : δ ≤ 1 := min_le_right _ _
  have hzero : ∀ d, p - q' ≤ d → d + Real.pi ≤ q - p' → (phase d * β).re = 0 := by
    intro d hd1 hd2
    have a := hG d hd1 (by linarith [Real.pi_pos])
    have b := hG (d + Real.pi) (by linarith [Real.pi_pos]) hd2
    rw [phase_add_pi, neg_mul, Complex.neg_re] at b
    linarith
  have hβ : β = 0 := by
    refine eq_zero_of_two_angles (p - q') (p - q' + δ) β ?_ (hzero _ le_rfl (by
      simp only [L] at hL; linarith)) (hzero _ (by linarith) (by simp only [L] at hδL; linarith))
    rw [add_sub_cancel_left]
    exact (Real.sin_pos_of_pos_of_lt_pi hδ (by linarith [Real.pi_gt_three])).ne'
  -- the pairing vanishes, so `H_Y(t) = 0` on the arc of `Y`
  set s0 := (p' + q') / 2
  have hHY : ∀ t ∈ Set.Icc p q, hermitianReal (phase t • Y) = 0 := by
    intro t ht
    obtain ⟨w, hw, hw0⟩ := psd_trace_qf _ (hsubY ht)
    apply hw0
    by_contra hne
    push Not at hne
    obtain ⟨k, hk⟩ := hne
    have htr := hw (hermitianReal (phase s0 • X))
    have hβ' : (Y * Xᴴ).trace = 0 := hβ
    rw [trace_identity X Y hYX, hβ', mul_zero, Complex.zero_re, zero_div,
      Complex.ofReal_zero] at htr
    have hre := congrArg Complex.re htr
    rw [Complex.zero_re, Complex.re_sum] at hre
    have hnn : ∀ j ∈ Finset.univ, 0 ≤ (qf (hermitianReal (phase s0 • X)) (w j)).re :=
      fun j _ => qf_psd_re_nonneg _ (hsubX ⟨by simp only [s0]; linarith,
        by simp only [s0]; linarith⟩) _
    have hk0 := (Finset.sum_eq_zero_iff_of_nonneg hnn).1 hre.symm k (Finset.mem_univ k)
    have hpos := interior_pos X h0 p' q' s0 hsubX (by simp only [s0]; linarith)
      (by simp only [s0]; linarith) (w k) hk
    have : (qf (hermitianReal (phase s0 • X)) (w k)).re = (phase s0 * qf X (w k)).re := by
      have := qf_hR X s0 (w k)
      rw [qf, this, Complex.ofReal_re]
    linarith
  set δ' := min (q - p) 1
  have hδ' : 0 < δ' := lt_min (by linarith) one_pos
  have hδ'1 : δ' ≤ 1 := min_le_right _ _
  have hδ'q : δ' ≤ q - p := min_le_left _ _
  apply hY
  refine eq_zero_of_qf Y fun v => ?_
  refine eq_zero_of_two_angles p (p + δ') _ ?_ (hR_zero_iff Y p (hHY p ⟨le_rfl, hpq.le⟩) v)
    (hR_zero_iff Y _ (hHY _ ⟨by linarith, by linarith⟩) v)
  rw [add_sub_cancel_left]
  exact (Real.sin_pos_of_pos_of_lt_pi hδ' (by linarith [Real.pi_gt_three])).ne'

/-! ### part (ii): existence -/

lemma isClosed_psd : IsClosed {P : Matrix ι ι ℂ | P.PosSemidef} := by
  have : {P : Matrix ι ι ℂ | P.PosSemidef} =
      {P | Pᴴ = P} ∩ ⋂ x : ι → ℂ, {P | 0 ≤ star x ⬝ᵥ (P *ᵥ x)} := by
    ext P
    simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter,
      Matrix.posSemidef_iff_dotProduct_mulVec]
    rfl
  rw [this]
  refine IsClosed.inter (isClosed_eq continuous_id.matrix_conjTranspose continuous_id)
    (isClosed_iInter fun x => isClosed_le continuous_const ?_)
  exact continuous_const.dotProduct (continuous_id.matrix_mulVec continuous_const)

lemma psd_decomp (A : Matrix ι ι ℂ) (hA : A.PosSemidef) :
    ∃ B : Matrix ι ι ℂ, A = Bᴴ * B := by
  open scoped MatrixOrder in
  have h0 : 0 ≤ A := Matrix.nonneg_iff_posSemidef.mpr hA
  open scoped MatrixOrder in
  have hB : (CFC.sqrt A).PosSemidef := Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg A)
  open scoped MatrixOrder in
  have hAB : A = (CFC.sqrt A)ᴴ * CFC.sqrt A := by
    rw [hB.isHermitian.eq, CFC.sqrt_mul_sqrt_self A h0]
  exact ⟨_, hAB⟩

lemma entry_bound (A : Matrix ι ι ℂ) (hA : A.PosSemidef) (i j : ι) :
    ‖A i j‖ ≤ 2 * (A.trace).re := by
  obtain ⟨B, rfl⟩ := psd_decomp A hA
  have hij : (Bᴴ * B) i j = ∑ k, star (B k i) * B k j := by
    simp [Matrix.mul_apply, Matrix.conjTranspose_apply]
  have htr : ((Bᴴ * B).trace).re = ∑ l, ∑ k, ‖B k l‖ ^ 2 := by
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Complex.re_sum]
    refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun k _ => ?_
    rw [Complex.star_def, Complex.conj_mul']
    norm_cast
  rw [hij, htr, Finset.sum_comm]
  calc ‖∑ k, star (B k i) * B k j‖ ≤ ∑ k, ‖star (B k i) * B k j‖ := norm_sum_le _ _
    _ ≤ ∑ k, (‖B k i‖ ^ 2 + ‖B k j‖ ^ 2) := by
        refine Finset.sum_le_sum fun k _ => ?_
        rw [norm_mul, norm_star]
        nlinarith [sq_nonneg (‖B k i‖ - ‖B k j‖), norm_nonneg (B k i), norm_nonneg (B k j)]
    _ ≤ ∑ k, (∑ l, ‖B k l‖ ^ 2 + ∑ l, ‖B k l‖ ^ 2) := by
        refine Finset.sum_le_sum fun k _ => add_le_add ?_ ?_
        · exact Finset.single_le_sum (f := fun l => ‖B k l‖ ^ 2)
            (fun l _ => sq_nonneg _) (Finset.mem_univ i)
        · exact Finset.single_le_sum (f := fun l => ‖B k l‖ ^ 2)
            (fun l _ => sq_nonneg _) (Finset.mem_univ j)
    _ = 2 * ∑ k, ∑ l, ‖B k l‖ ^ 2 := by
        rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun k _ => ?_; ring

lemma omega_compact (a : ℝ) : IsCompact (omega (ι := ι) a) := by
  by_cases h : 0 ≤ a ∧ a < Real.pi
  · let K : Set (Matrix ι ι ℂ × Matrix ι ι ℂ) :=
      {p | p.1.PosSemidef ∧ p.2.PosSemidef ∧ p.1.trace + p.2.trace = 1}
    have hom : omega (ι := ι) a =
        (fun p : Matrix ι ι ℂ × Matrix ι ι ℂ => blend a p.1 p.2) '' K := by
      ext R
      simp only [omega, Set.mem_setOf_eq, Set.mem_image, K, Prod.exists]
      constructor
      · rintro ⟨-, -, P, Q, hP, hQ, htr, rfl⟩
        exact ⟨P, Q, ⟨hP, hQ, htr⟩, rfl⟩
      · rintro ⟨P, Q, ⟨hP, hQ, htr⟩, rfl⟩
        exact ⟨h.1, h.2, P, Q, hP, hQ, htr, rfl⟩
    rw [hom]
    let Bs : Set (Matrix ι ι ℂ) :=
      Set.pi Set.univ fun _ => Set.pi Set.univ fun _ => Metric.closedBall (0 : ℂ) 2
    have hBs : IsCompact Bs :=
      isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_closedBall _ _
    have hKc : IsClosed K := by
      refine (isClosed_psd.preimage continuous_fst).inter
        ((isClosed_psd.preimage continuous_snd).inter (isClosed_eq ?_ continuous_const))
      exact continuous_fst.matrix_trace.add continuous_snd.matrix_trace
    have hbd : ∀ P Q : Matrix ι ι ℂ, P.PosSemidef → Q.PosSemidef →
        P.trace + Q.trace = 1 → P ∈ Bs := by
      intro P Q hP hQ htr
      simp only [Bs, Set.mem_pi]
      intro i _ j _
      rw [Metric.mem_closedBall, dist_zero_right]
      have h1 := entry_bound P hP i j
      have h2 : 0 ≤ (Q.trace).re := (Complex.nonneg_iff.mp hQ.trace_nonneg).1
      have h3 : (P.trace).re + (Q.trace).re = 1 := by
        have := congrArg Complex.re htr; simpa using this
      linarith
    have hKs : K ⊆ Bs ×ˢ Bs := by
      rintro ⟨P, Q⟩ ⟨hP, hQ, htr⟩
      exact ⟨hbd P Q hP hQ htr, hbd Q P hQ hP (by rw [add_comm]; exact htr)⟩
    refine IsCompact.image ((hBs.prod hBs).of_isClosed_subset hKc hKs) ?_
    simp only [blend]
    fun_prop
  · convert isCompact_empty
    ext R
    simp only [omega, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
    rintro ⟨h1, h2, -⟩
    exact h ⟨h1, h2⟩

lemma omega_convex (a : ℝ) : Convex ℝ (omega (ι := ι) a) := by
  rintro R1 ⟨ha0, hapi, P1, Q1, hP1, hQ1, htr1, rfl⟩ R2 ⟨-, -, P2, Q2, hP2, hQ2, htr2, rfl⟩
    s t hs ht hst
  refine ⟨ha0, hapi, s • P1 + t • P2, s • Q1 + t • Q2, (hP1.smul hs).add (hP2.smul ht),
    (hQ1.smul hs).add (hQ2.smul ht), ?_, ?_⟩
  · simp only [Matrix.trace_add, Matrix.trace_smul, Complex.real_smul]
    have : (s : ℂ) + t = 1 := by exact_mod_cast hst
    linear_combination (s : ℂ) * htr1 + (t : ℂ) * htr2 + this
  · simp only [blend, smul_add]
    rw [smul_comm (phase (a / 2)) s P1, smul_comm (phase (a / 2)) t P2,
      smul_comm (phase (-a / 2)) s Q1, smul_comm (phase (-a / 2)) t Q2]
    abel


lemma margin (t η : ℝ) (z : ℂ) :
    (phase t * z).re - |η| * ‖z‖ ≤ (phase (t + η) * z).re := by
  have h1 : phase (t + η) * z - phase t * z = phase t * (phase η - 1) * z := by
    rw [← phase_mul]; ring
  have hn : ‖phase t * (phase η - 1) * z‖ ≤ |η| * ‖z‖ := by
    rw [norm_mul, norm_mul]
    have : ‖phase t‖ = 1 := by unfold phase; exact Complex.norm_exp_ofReal_mul_I t
    rw [this, one_mul]
    have h2 : ‖phase η - 1‖ ≤ |η| := by
      have := Real.norm_exp_I_mul_ofReal_sub_one_le (x := η)
      unfold phase; rw [mul_comm]; simpa [Real.norm_eq_abs] using this
    exact mul_le_mul_of_nonneg_right h2 (norm_nonneg _)
  have h3 := Complex.abs_re_le_norm (phase t * (phase η - 1) * z)
  have h4 : (phase (t + η) * z).re - (phase t * z).re = (phase t * (phase η - 1) * z).re := by
    rw [← Complex.sub_re, h1]
  have := neg_abs_le (phase t * (phase η - 1) * z).re
  linarith

lemma qf_zero (X : Mat ι) : qf X 0 = 0 := by simp [qf]

theorem part2 [Nonempty ι] (X : Mat ι) (a : ℝ) (ha : Real.pi - width X ≤ a)
    (hap : a < Real.pi) : ∃ R ∈ omega (ι := ι) a, (R * X).trace = 0 := by
  have hwle : width X ≤ Real.pi := by
    unfold width; split_ifs
    · exact le_rfl
    · have : 0 ≤ gammaLength X := ENNReal.toReal_nonneg
      linarith
  have ha0 : 0 ≤ a := by linarith
  by_cases h0 : (0 : ℂ) ∈ numericalRange X
  · obtain ⟨D, ⟨hDpsd, hDtr⟩, hDX⟩ := h0
    have hhalf : (0 : ℂ) ≤ (1 / 2 : ℂ) := by
      rw [show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by push_cast; ring]
      exact_mod_cast (by norm_num : (0 : ℝ) ≤ 1 / 2)
    refine ⟨blend a ((1 / 2 : ℂ) • D) ((1 / 2 : ℂ) • D), ⟨ha0, hap, _, _, hDpsd.smul hhalf,
      hDpsd.smul hhalf, ?_, rfl⟩, ?_⟩
    · rw [Matrix.trace_smul, hDtr]; norm_num
    · simp only [blend, Matrix.add_mul, Matrix.smul_mul, Matrix.trace_add, Matrix.trace_smul,
        hDX, smul_zero, add_zero]
  have hgl : gammaLength X ≤ a := by
    unfold width at ha; rw [if_neg h0] at ha; linarith
  by_contra hno
  push Not at hno
  -- separation of the trace image from the origin
  let f : Mat ι →ₗ[ℝ] ℂ :=
    ((Matrix.traceLinearMap ι ℂ ℂ).comp (LinearMap.mulRight ℂ X)).restrictScalars ℝ
  have hf : ∀ R, f R = (R * X).trace := fun R => rfl
  set S := (fun R : Mat ι => (R * X).trace) '' omega (ι := ι) a
  have hSconv : Convex ℝ S := by
    have := (omega_convex (ι := ι) a).linear_image f
    simpa [S, hf] using this
  have hScomp : IsCompact S :=
    (omega_compact a).image ((continuous_id.matrix_mul continuous_const).matrix_trace)
  have hdisj : Disjoint S {0} := by
    rw [Set.disjoint_singleton_right]
    rintro ⟨R, hR, hR0⟩
    exact hno R hR hR0
  obtain ⟨g, u, v, hgu, huv, hgv⟩ := RCLike.geometric_hahn_banach_compact_closed (𝕜 := ℂ)
    hSconv hScomp (convex_singleton 0) isClosed_singleton hdisj
  have hv0 : v < 0 := by simpa using hgv 0 rfl
  set c := -(g 1)
  have hgc : ∀ z : ℂ, g z = z * g 1 := by
    intro z
    have := g.map_smul z 1
    rw [smul_eq_mul, mul_one, smul_eq_mul] at this
    exact this
  set δ0 := -u
  have hδ0 : 0 < δ0 := by simp only [δ0]; linarith
  have hS : ∀ z ∈ S, δ0 < (c * z).re := by
    intro z hz
    have := hgu z hz
    rw [hgc, mul_comm, RCLike.re_to_complex] at this
    simp only [c, δ0, neg_mul, Complex.neg_re]
    linarith
  -- membership of pure-part probes
  have hmem1 : ∀ w : ι → ℂ, w ≠ 0 → blend a (dens w) 0 ∈ omega (ι := ι) a := fun w hw =>
    ⟨ha0, hap, _, _, dens_psd w, Matrix.PosSemidef.zero, by rw [dens_trace hw]; simp, rfl⟩
  have hmem2 : ∀ w : ι → ℂ, w ≠ 0 → blend a 0 (dens w) ∈ omega (ι := ι) a := fun w hw =>
    ⟨ha0, hap, _, _, Matrix.PosSemidef.zero, dens_psd w, by rw [dens_trace hw]; simp, rfl⟩
  have htr1 : ∀ w, (blend a (dens w) 0 * X).trace =
      phase (a / 2) * ((((nrm w)⁻¹ : ℝ) : ℂ) * qf X w) := by
    intro w
    simp only [blend, smul_zero, add_zero, Matrix.smul_mul, Matrix.trace_smul, dens_trace_mul,
      smul_eq_mul]
  have htr2 : ∀ w, (blend a 0 (dens w) * X).trace =
      phase (-a / 2) * ((((nrm w)⁻¹ : ℝ) : ℂ) * qf X w) := by
    intro w
    simp only [blend, smul_zero, zero_add, Matrix.smul_mul, Matrix.trace_smul, dens_trace_mul,
      smul_eq_mul]
  obtain ⟨i0⟩ := ‹Nonempty ι›
  have hw0 : (Pi.single i0 (1 : ℂ) : ι → ℂ) ≠ 0 := by
    intro h; have := congrFun h i0; simp at this
  have hc0 : c ≠ 0 := by
    intro hc
    have := hS _ ⟨_, hmem1 _ hw0, rfl⟩
    rw [hc, zero_mul, Complex.zero_re] at this
    linarith
  have hcn : 0 < ‖c‖ := norm_pos_iff.2 hc0
  set θ := Complex.arg c
  have hcpol : c = (‖c‖ : ℂ) * phase θ := (Complex.norm_mul_exp_arg_mul_I c).symm
  set δ1 := δ0 / ‖c‖
  have hδ1 : 0 < δ1 := div_pos hδ0 hcn
  -- strict positivity at the two endpoint angles
  have hend : ∀ (b : ℝ) (R : (ι → ℂ) → Mat ι),
      (∀ w, w ≠ 0 → R w ∈ omega (ι := ι) a) →
      (∀ w, (R w * X).trace = phase b * ((((nrm w)⁻¹ : ℝ) : ℂ) * qf X w)) →
      ∀ w : ι → ℂ, w ≠ 0 → δ1 * nrm w < (phase (θ + b) * qf X w).re := by
    intro b R hR htr w hw
    have h := hS _ ⟨_, hR w hw, rfl⟩
    simp only at h
    rw [htr, hcpol] at h
    have hN := nrm_pos hw
    have heq : ((‖c‖ : ℂ) * phase θ * (phase b * ((((nrm w)⁻¹ : ℝ) : ℂ) * qf X w))).re =
        ‖c‖ * (nrm w)⁻¹ * (phase (θ + b) * qf X w).re := by
      rw [← phase_mul]
      rw [show (‖c‖ : ℂ) * phase θ * (phase b * ((((nrm w)⁻¹ : ℝ) : ℂ) * qf X w)) =
          ((‖c‖ * (nrm w)⁻¹ : ℝ) : ℂ) * (phase θ * phase b * qf X w) by push_cast; ring]
      rw [Complex.re_ofReal_mul]
    rw [heq] at h
    have : δ0 * nrm w < ‖c‖ * (phase (θ + b) * qf X w).re := by
      have h' := mul_lt_mul_of_pos_right h hN
      rw [show ‖c‖ * (nrm w)⁻¹ * (phase (θ + b) * qf X w).re * nrm w =
        ‖c‖ * (phase (θ + b) * qf X w).re by field_simp] at h'
      exact h'
    simp only [δ1]
    rw [div_mul_eq_mul_div, div_lt_iff₀ hcn]
    linarith
  have hp1 := hend (a / 2) (fun w => blend a (dens w) 0) hmem1 htr1
  have hp2 := hend (-a / 2) (fun w => blend a 0 (dens w)) hmem2 htr2
  set K := ∑ i, ∑ j, ‖X i j‖
  have hK : 0 ≤ K := Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _
  set ε := min (δ1 / (2 * K + 1)) ((Real.pi - a) / 4)
  have hε : 0 < ε := lt_min (div_pos hδ1 (by linarith)) (by linarith)
  have hεK : ε * (2 * K + 1) ≤ δ1 := by
    have := min_le_left (δ1 / (2 * K + 1)) ((Real.pi - a) / 4)
    rwa [le_div_iff₀ (by linarith)] at this
  have hεπ : ε ≤ (Real.pi - a) / 4 := min_le_right _ _
  have hext : ∀ b η : ℝ, |η| = ε →
      (∀ w : ι → ℂ, w ≠ 0 → δ1 * nrm w < (phase (θ + b) * qf X w).re) →
      θ + b + η ∈ A X := by
    intro b η hη hb
    rw [mem_A]
    intro w
    by_cases hw : w = 0
    · rw [hw, qf_zero, mul_zero, Complex.zero_re]
    have h1 := hb w hw
    have h2 := margin (θ + b) η (qf X w)
    have h3 := qf_bound X w
    have hN := nrm_pos hw
    rw [hη] at h2
    have : ε * ‖qf X w‖ ≤ ε * (2 * K * nrm w) := by
      apply mul_le_mul_of_nonneg_left _ hε.le; linarith
    nlinarith
  have hA1 : θ + a / 2 + ε ∈ A X := hext (a / 2) ε (abs_of_pos hε) hp1
  have hA2 : θ + -a / 2 + -ε ∈ A X := hext (-a / 2) (-ε) (by rw [abs_neg, abs_of_pos hε]) hp2
  have hsub : Set.Icc (θ + -a / 2 + -ε) (θ + -a / 2 + -ε + (a + 2 * ε)) ⊆ A X := by
    intro t ht
    refine arcA X _ t (θ + a / 2 + ε) ht.1 (by linarith [ht.2]) (by linarith) hA2 hA1
  have := gL_lower X _ (a + 2 * ε) (by linarith) (by linarith [Real.pi_pos]) hsub
  linarith

end X6P75L

open QAlgorithms.Papers.Independent.Information100.P75 in
theorem solution {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (X : Mat ι) :
    (∀ Y : Mat ι, Y ≠ 0 → (Y * X).trace = 0 → Real.pi - width X ≤ closedWidth Y) ∧
    (0 < width X → ∀ a : ℝ, Real.pi - width X ≤ a → a < Real.pi →
      ∃ R ∈ omega (ι := ι) a, (R * X).trace = 0) :=
  ⟨fun Y hY hYX => X6P75L.part1 X Y hY hYX, fun _ a ha hap => X6P75L.part2 X a ha hap⟩
