-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Information100.P75.basicWidthFacts
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-20T07:44:26.44441+00:00
-- url     : https://prove2.me/submissions/843be1d1-3292-4b7e-9cda-35a946acc567

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P75

noncomputable section

open QAlgorithms QAlgorithms.Papers QAlgorithms.Papers.Independent QAlgorithms.Papers.Independent.Information100 QAlgorithms.Papers.Independent.Information100.P75

open Classical

open scoped ComplexConjugate ComplexOrder Matrix

open MeasureTheory

lemma g53e_phase_pi (t : ℝ) : phase (t + Real.pi) = -phase t := by
  unfold phase
  rw [Complex.ofReal_add, add_mul, Complex.exp_add, Complex.exp_pi_mul_I]; ring

lemma g53e_herm_neg {ι : Type*} (Y : Mat ι) : hermitianReal (-Y) = -hermitianReal Y := by
  unfold hermitianReal
  rw [Matrix.conjTranspose_neg, ← neg_add, smul_neg]

lemma g53e_herm_isH {ι : Type*} (Y : Mat ι) : (hermitianReal Y).IsHermitian := by
  unfold hermitianReal Matrix.IsHermitian
  rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_add, Matrix.conjTranspose_conjTranspose, add_comm]
  congr 1
  simp

lemma g53e_zero_unique {ι : Type*} [Fintype ι] (X : Mat ι) (hX : X ≠ 0) (t s : ℝ)
    (ht : hermitianReal (phase t • X) = 0) (hs : hermitianReal (phase s • X) = 0)
    (h1 : -Real.pi < s - t) (h2 : s - t < Real.pi) : t = s := by
  unfold hermitianReal at ht hs
  rw [smul_eq_zero] at ht hs
  rcases ht with ht | ht
  · norm_num at ht
  rcases hs with hs | hs
  · norm_num at hs
  rw [Matrix.conjTranspose_smul] at ht hs
  set c := phase t
  set e := phase s
  have hc : star c * c = 1 := by
    simp only [c, phase, ← Complex.exp_conj, Complex.star_def, ← Complex.exp_add]
    rw [map_mul, Complex.conj_ofReal, Complex.conj_I]
    rw [show (t : ℂ) * -Complex.I + ↑t * Complex.I = 0 by ring, Complex.exp_zero]
  have he : star e * e = 1 := by
    simp only [e, phase, ← Complex.exp_conj, Complex.star_def, ← Complex.exp_add]
    rw [map_mul, Complex.conj_ofReal, Complex.conj_I]
    rw [show (s : ℂ) * -Complex.I + ↑s * Complex.I = 0 by ring, Complex.exp_zero]
  have hXH : Xᴴ = -(c * c) • X := by
    have h3 : star c • Xᴴ = -(c • X) := eq_neg_of_add_eq_zero_right ht
    have h4 := congrArg (fun M => c • M) h3
    simp only [smul_smul, smul_neg] at h4
    rw [mul_comm c (star c), hc, one_smul] at h4
    rw [h4, neg_smul]
  rw [hXH, smul_smul, ← add_smul, smul_eq_zero] at hs
  rcases hs with hs | hs
  · have hee : e * e = c * c := by linear_combination e * hs + (c * c) * he
    simp only [e, c, phase, ← Complex.exp_add] at hee
    obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.mp hee
    have him := congrArg Complex.im hn
    simp at him
    have hn1 : (n : ℝ) * Real.pi < Real.pi := by nlinarith
    have hn2 : -Real.pi < (n : ℝ) * Real.pi := by nlinarith
    have hp := Real.pi_pos
    have a1 : (n : ℝ) < 1 := by
      by_contra h; push Not at h; nlinarith
    have a2 : (-1 : ℝ) < n := by
      by_contra h; push Not at h; nlinarith
    have : n = 0 := by
      have : n < 1 := by exact_mod_cast a1
      have : -1 < n := by exact_mod_cast a2
      omega
    subst this
    simp at him
    linarith
  · exact absurd hs hX

lemma g55d_phase_mul (s t : ℝ) : phase s * phase t = phase (s + t) := by
  unfold phase; rw [← Complex.exp_add]; push_cast; ring_nf

lemma g55d_star_phase (t : ℝ) : star (phase t) = phase (-t) := by
  unfold phase; rw [Complex.star_def, ← Complex.exp_conj]; congr 1
  rw [map_mul, Complex.conj_ofReal, Complex.conj_I]; push_cast; ring

lemma g55d_cos_phase (t : ℝ) : ((Real.cos t : ℝ) : ℂ) = (phase t + phase (-t)) / 2 := by
  unfold phase; rw [Complex.ofReal_cos, Complex.cos]; push_cast; ring_nf

lemma g55d_phase_re (t : ℝ) : (phase t).re = Real.cos t := by
  unfold phase; exact Complex.exp_ofReal_mul_I_re t

lemma g55d_phase_im (t : ℝ) : (phase t).im = Real.sin t := by
  unfold phase; exact Complex.exp_ofReal_mul_I_im t

lemma g55d_herm_add {ι : Type*} (X Y : Mat ι) :
    hermitianReal (X + Y) = hermitianReal X + hermitianReal Y := by
  unfold hermitianReal; rw [Matrix.conjTranspose_add, ← smul_add]; congr 1; abel

lemma g55d_herm_smul {ι : Type*} (w : ℂ) (P : Mat ι) (hP : P.IsHermitian) :
    hermitianReal (w • P) = ((w + star w) / 2) • P := by
  unfold hermitianReal
  rw [Matrix.conjTranspose_smul, hP.eq, ← add_smul, smul_smul]; congr 1; ring

lemma g55d_herm_phase_blend {ι : Type*} (a t : ℝ) (P Q : Mat ι) (hP : P.IsHermitian)
    (hQ : Q.IsHermitian) :
    hermitianReal (phase t • blend a P Q) =
      ((Real.cos (t + a / 2) : ℝ) : ℂ) • P + ((Real.cos (t - a / 2) : ℝ) : ℂ) • Q := by
  have e : phase t • blend a P Q = phase (t + a / 2) • P + phase (t - a / 2) • Q := by
    unfold blend
    rw [smul_add, smul_smul, smul_smul, g55d_phase_mul, g55d_phase_mul]
    congr 3; ring
  rw [e, g55d_herm_add, g55d_herm_smul _ _ hP, g55d_herm_smul _ _ hQ, g55d_star_phase,
    g55d_star_phase, g55d_cos_phase, g55d_cos_phase]


lemma g55d_trace_real {ι : Type*} [Fintype ι] (P : Mat ι) (hP : P.PosSemidef) :
    0 ≤ P.trace.re ∧ P.trace.im = 0 := by
  have h := hP.trace_nonneg
  rw [Complex.nonneg_iff] at h
  exact ⟨h.1, h.2.symm⟩

lemma g55d_tr_herm {ι : Type*} [Fintype ι] (R Y : Mat ι) (hR : R.IsHermitian) :
    (R * hermitianReal Y).trace = (((R * Y).trace.re : ℝ) : ℂ) := by
  unfold hermitianReal
  rw [Matrix.mul_smul, Matrix.mul_add, Matrix.trace_smul, Matrix.trace_add]
  have : (R * Yᴴ).trace = star (R * Y).trace := by
    rw [← Matrix.trace_conjTranspose, Matrix.conjTranspose_mul, hR.eq, Matrix.trace_mul_comm]
  rw [this, Complex.star_def, Complex.add_conj, smul_eq_mul]; push_cast; ring

lemma g55d_K1 {ι : Type*} [Fintype ι] [DecidableEq ι] (Y : Mat ι) :
    (∀ R : Mat ι, IsDensityMatrix R → 0 ≤ ((R * Y).trace).re) ↔ (hermitianReal Y).PosSemidef := by
  constructor
  · intro h
    have hH := g53e_herm_isH Y
    refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hH fun x => ?_
    rw [Complex.nonneg_iff]
    refine ⟨?_, (hH.im_star_dotProduct_mulVec_self x).symm⟩
    by_cases hx : x = 0
    · simp [hx]
    set s : ℝ := ∑ i, ‖x i‖ ^ 2 with hs
    have hspos : 0 < s := by
      obtain ⟨i, hi⟩ := Function.ne_iff.mp hx
      have : 0 < ‖x i‖ ^ 2 := by positivity
      exact lt_of_lt_of_le this (Finset.single_le_sum (f := fun i => ‖x i‖ ^ 2)
        (fun i _ => by positivity) (Finset.mem_univ i))
    have htr : (Matrix.vecMulVec x (star x)).trace = (s : ℂ) := by
      rw [Matrix.trace_vecMulVec, hs]; push_cast
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [Pi.star_apply]; rw [Complex.star_def, Complex.mul_conj']
    let R : Mat ι := ((s⁻¹ : ℝ) : ℂ) • Matrix.vecMulVec x (star x)
    have hRd : IsDensityMatrix R := by
      refine ⟨(Matrix.posSemidef_vecMulVec_self_star x).smul
        (Complex.zero_le_real.mpr (inv_nonneg.mpr hspos.le)), ?_⟩
      simp only [R]; rw [Matrix.trace_smul, htr, smul_eq_mul]; push_cast
      field_simp
    have h1 := h R hRd
    rw [← Complex.ofReal_re ((R * Y).trace.re), ← g55d_tr_herm R Y hRd.1.1] at h1
    have e : (R * hermitianReal Y).trace = ((s⁻¹ : ℝ) : ℂ) * (star x ⬝ᵥ (hermitianReal Y *ᵥ x)) := by
      simp only [R]
      rw [Matrix.smul_mul, Matrix.trace_smul, Matrix.vecMulVec_mul, Matrix.trace_vecMulVec,
        smul_eq_mul, Matrix.dotProduct_mulVec, dotProduct_comm]
    rw [e, Complex.re_ofReal_mul] at h1
    exact (mul_nonneg_iff_of_pos_left (inv_pos.mpr hspos)).mp h1
  · intro hH R hR
    rw [← Complex.ofReal_re ((R * Y).trace.re), ← g55d_tr_herm R Y hR.1.1]
    open scoped MatrixOrder in
    obtain ⟨B, hB⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hR.1.nonneg
    have hB' : R = Bᴴ * B := hB
    rw [hB', Matrix.mul_assoc, Matrix.trace_mul_comm, Matrix.mul_assoc]
    have := (hH.mul_mul_conjTranspose_same B).trace_nonneg
    rw [Matrix.mul_assoc] at this
    exact (Complex.nonneg_iff.mp this).1

lemma g55d_clause4 {ι : Type*} [Fintype ι] [DecidableEq ι] (X : Mat ι) :
    (∀ z ∈ numericalRange X, 0 ≤ z.re) ↔ (hermitianReal X).PosSemidef := by
  rw [← g55d_K1]
  constructor
  · intro h R hR; exact h _ ⟨R, hR, rfl⟩
  · rintro h _ ⟨R, hR, rfl⟩; exact h R hR


lemma g55d_clause5 {ι : Type*} [Fintype ι] [DecidableEq ι] (X : Mat ι) (hX : X ≠ 0)
    (hw : closedWidth X < Real.pi) : X.trace ≠ 0 := by
  intro h0
  have hp := Real.pi_pos
  have hz : ∀ t ∈ gammaSet X, hermitianReal (phase t • X) = 0 := by
    intro t ht
    refine (ht.2.2.trace_eq_zero_iff).1 ?_
    unfold hermitianReal
    rw [Matrix.trace_smul, Matrix.trace_add, Matrix.trace_conjTranspose, Matrix.trace_smul, h0]
    simp
  have hP : ∀ c, volume (gammaSet X ∩ Set.Ico c (c + Real.pi / 2)) = 0 := by
    intro c
    apply Set.Subsingleton.measure_zero
    rintro t ⟨ht, ht1, ht2⟩ s ⟨hs, hs1, hs2⟩
    exact g53e_zero_unique X hX t s (hz t ht) (hz s hs) (by linarith) (by linarith)
  have hsub : gammaSet X ⊆ ((gammaSet X ∩ Set.Ico (-Real.pi) (-Real.pi + Real.pi / 2) ∪
      gammaSet X ∩ Set.Ico (-Real.pi / 2) (-Real.pi / 2 + Real.pi / 2)) ∪
      gammaSet X ∩ Set.Ico 0 (0 + Real.pi / 2)) ∪
      gammaSet X ∩ Set.Ico (Real.pi / 2) (Real.pi / 2 + Real.pi / 2) := by
    intro t ht
    have ht' := ht
    obtain ⟨h1, h2, -⟩ := ht'
    simp only [Set.mem_union, Set.mem_inter_iff, Set.mem_Ico]
    rcases lt_or_ge t (-Real.pi / 2) with a | a
    · left; left; left; exact ⟨ht, h1, by linarith⟩
    rcases lt_or_ge t 0 with b | b
    · left; left; right; exact ⟨ht, a, by linarith⟩
    rcases lt_or_ge t (Real.pi / 2) with c | c
    · left; right; exact ⟨ht, b, by linarith⟩
    · right; exact ⟨ht, c, by linarith⟩
  have hnull : volume (gammaSet X) = 0 :=
    measure_mono_null hsub (measure_union_null (measure_union_null
      (measure_union_null (hP _) (hP _)) (hP _)) (hP _))
  unfold closedWidth gammaLength at hw
  rw [hnull] at hw
  simp at hw

lemma g55d_herm_cong {ι : Type*} [Fintype ι] (G X : Mat ι) (t : ℝ) :
    hermitianReal (phase t • (G * X * Gᴴ)) = G * hermitianReal (phase t • X) * Gᴴ := by
  unfold hermitianReal
  simp only [Matrix.conjTranspose_smul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
    Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]

lemma g55d_inv_eq {ι : Type*} [Fintype ι] [DecidableEq ι] (G X : Mat ι) (hG : IsUnit G.det) :
    G⁻¹ * (G * X * Gᴴ) * (G⁻¹)ᴴ = X := by
  have hGh : IsUnit Gᴴ.det := by rw [Matrix.det_conjTranspose]; exact hG.star
  rw [Matrix.conjTranspose_nonsing_inv]
  rw [show G⁻¹ * (G * X * Gᴴ) * (Gᴴ)⁻¹ = (G⁻¹ * G) * X * (Gᴴ * (Gᴴ)⁻¹) by
    simp only [Matrix.mul_assoc]]
  rw [Matrix.nonsing_inv_mul _ hG, Matrix.mul_nonsing_inv _ hGh, Matrix.one_mul, Matrix.mul_one]

lemma g55d_W_cong {ι : Type*} [Fintype ι] [DecidableEq ι] (G X : Mat ι) (hG : IsUnit G.det)
    (h : 0 ∈ numericalRange X) : 0 ∈ numericalRange (G * X * Gᴴ) := by
  obtain ⟨R, hR, h0⟩ := h
  set G' := G⁻¹
  set R1 := G'ᴴ * R * G'
  have hR1 : R1.PosSemidef := hR.1.conjTranspose_mul_mul_same G'
  have htr1 : (R1 * (G * X * Gᴴ)).trace = 0 := by
    have e : R1 * (G * X * Gᴴ) = G'ᴴ * (R * (G' * G) * X * Gᴴ) := by
      simp only [R1, Matrix.mul_assoc]
    rw [e, Matrix.trace_mul_comm, Matrix.nonsing_inv_mul _ hG, Matrix.mul_one]
    rw [show R * X * Gᴴ * G'ᴴ = R * X * (G' * G)ᴴ by
      rw [Matrix.conjTranspose_mul]; simp only [Matrix.mul_assoc]]
    rw [Matrix.nonsing_inv_mul _ hG, Matrix.conjTranspose_one, Matrix.mul_one, h0]
  have hR1ne : R1 ≠ 0 := by
    intro h1
    have : R = Gᴴ * R1 * G := by
      simp only [R1]
      rw [show Gᴴ * (G'ᴴ * R * G') * G = (G' * G)ᴴ * R * (G' * G) by
        rw [Matrix.conjTranspose_mul]; simp only [Matrix.mul_assoc]]
      rw [Matrix.nonsing_inv_mul _ hG]; simp
    rw [this, h1, Matrix.mul_zero, Matrix.zero_mul] at hR
    simpa using hR.2
  have htrne : R1.trace ≠ 0 := fun h => hR1ne ((hR1.trace_eq_zero_iff).1 h)
  have htrr := g55d_trace_real R1 hR1
  have hre : 0 < R1.trace.re := by
    rcases htrr.1.lt_or_eq with h | h
    · exact h
    · exact absurd (Complex.ext h.symm htrr.2) htrne
  have htreq : R1.trace = ((R1.trace.re : ℝ) : ℂ) := Complex.ext rfl (by simp [htrr.2])
  refine ⟨((R1.trace.re)⁻¹ : ℝ) • R1, ⟨?_, ?_⟩, ?_⟩
  · have : (((R1.trace.re)⁻¹ : ℝ) • R1) = (((R1.trace.re)⁻¹ : ℝ) : ℂ) • R1 := by
      rw [← Complex.coe_smul]
    rw [this]; exact hR1.smul (Complex.zero_le_real.mpr (inv_nonneg.mpr hre.le))
  · rw [← Complex.coe_smul, Matrix.trace_smul, htreq, smul_eq_mul]; push_cast
    rw [Complex.ofReal_re]
    exact inv_mul_cancel₀ (by exact_mod_cast hre.ne')
  · rw [Matrix.smul_mul, Matrix.trace_smul, htr1, smul_zero]

lemma g55d_clause3 {ι : Type*} [Fintype ι] [DecidableEq ι] (X G : Mat ι) (hG : IsUnit G.det) :
    width X = width (G * X * Gᴴ) := by
  have hGi : IsUnit (G⁻¹).det := Matrix.isUnit_nonsing_inv_det G hG
  have hW : 0 ∈ numericalRange X ↔ 0 ∈ numericalRange (G * X * Gᴴ) := by
    constructor
    · exact g55d_W_cong G X hG
    · intro h
      have := g55d_W_cong G⁻¹ _ hGi h
      rwa [g55d_inv_eq G X hG] at this
  have hS : gammaSet X = gammaSet (G * X * Gᴴ) := by
    ext t
    simp only [gammaSet, Set.mem_ofPred_eq]
    refine and_congr_right fun _ => and_congr_right fun _ => ?_
    rw [g55d_herm_cong]
    constructor
    · intro h; exact h.mul_mul_conjTranspose_same G
    · intro h
      have := h.mul_mul_conjTranspose_same G⁻¹
      rw [g55d_inv_eq G _ hG] at this
      exact this
  unfold width gammaLength
  rw [← hS]
  simp only [hW]

lemma g55d_shift (G : Set ℝ) (hper : ∀ (s : ℝ) (k : ℤ), s + k * (2 * Real.pi) ∈ G ↔ s ∈ G)
    (k : ℤ) (u v : ℝ) :
    volume (Set.Ico (u + k * (2 * Real.pi)) (v + k * (2 * Real.pi)) ∩ G) =
      volume (Set.Ico u v ∩ G) := by
  rw [← measure_preimage_add_right volume (k * (2 * Real.pi))]
  congr 1
  ext t
  simp only [Set.mem_preimage, Set.mem_inter_iff, Set.mem_Ico, hper, add_le_add_iff_right,
    add_lt_add_iff_right]

lemma g55d_split (G : Set ℝ) (hper : ∀ (s : ℝ) (k : ℤ), s + k * (2 * Real.pi) ∈ G ↔ s ∈ G)
    (c c' : ℝ) (h1 : c ≤ c') (h2 : c' ≤ c + 2 * Real.pi) :
    volume (Set.Ico c (c + 2 * Real.pi) ∩ G) = volume (Set.Ico c' (c' + 2 * Real.pi) ∩ G) := by
  have hp := Real.pi_pos
  rw [← measure_inter_add_diff (Set.Ico c (c + 2 * Real.pi) ∩ G) (measurableSet_Ico (a := c) (b := c')),
    ← measure_inter_add_diff (Set.Ico c' (c' + 2 * Real.pi) ∩ G)
      (measurableSet_Ico (a := c') (b := c + 2 * Real.pi))]
  have e1 : Set.Ico c (c + 2 * Real.pi) ∩ G ∩ Set.Ico c c' = Set.Ico c c' ∩ G := by
    ext t; simp only [Set.mem_inter_iff, Set.mem_Ico]
    constructor
    · rintro ⟨⟨⟨a, b⟩, g⟩, d, e⟩; exact ⟨⟨d, e⟩, g⟩
    · rintro ⟨⟨d, e⟩, g⟩; exact ⟨⟨⟨d, by linarith⟩, g⟩, d, e⟩
  have e2 : (Set.Ico c (c + 2 * Real.pi) ∩ G) \ Set.Ico c c' = Set.Ico c' (c + 2 * Real.pi) ∩ G := by
    ext t; simp only [Set.mem_inter_iff, Set.mem_diff, Set.mem_Ico, not_and, not_lt]
    constructor
    · rintro ⟨⟨⟨a, b⟩, g⟩, d⟩; exact ⟨⟨d a, b⟩, g⟩
    · rintro ⟨⟨d, e⟩, g⟩; exact ⟨⟨⟨by linarith, e⟩, g⟩, fun _ => d⟩
  have e3 : Set.Ico c' (c' + 2 * Real.pi) ∩ G ∩ Set.Ico c' (c + 2 * Real.pi) =
      Set.Ico c' (c + 2 * Real.pi) ∩ G := by
    ext t; simp only [Set.mem_inter_iff, Set.mem_Ico]
    constructor
    · rintro ⟨⟨⟨a, b⟩, g⟩, d, e⟩; exact ⟨⟨d, e⟩, g⟩
    · rintro ⟨⟨d, e⟩, g⟩; exact ⟨⟨⟨d, by linarith⟩, g⟩, d, e⟩
  have e4 : (Set.Ico c' (c' + 2 * Real.pi) ∩ G) \ Set.Ico c' (c + 2 * Real.pi) =
      Set.Ico (c + ((1 : ℤ) : ℝ) * (2 * Real.pi)) (c' + ((1 : ℤ) : ℝ) * (2 * Real.pi)) ∩ G := by
    ext t; simp only [Set.mem_inter_iff, Set.mem_diff, Set.mem_Ico, not_and, not_lt,
      Int.cast_one, one_mul]
    constructor
    · rintro ⟨⟨⟨a, b⟩, g⟩, d⟩; exact ⟨⟨d a, b⟩, g⟩
    · rintro ⟨⟨d, e⟩, g⟩; exact ⟨⟨⟨by linarith, e⟩, g⟩, fun _ => d⟩
  rw [e1, e2, e3, e4, g55d_shift G hper, add_comm]

lemma g55d_Jconst (G : Set ℝ) (hper : ∀ (s : ℝ) (k : ℤ), s + k * (2 * Real.pi) ∈ G ↔ s ∈ G)
    (c : ℝ) : volume (Set.Ico c (c + 2 * Real.pi) ∩ G) = volume (Set.Ico (-Real.pi) Real.pi ∩ G) := by
  have hp := Real.pi_pos
  set k : ℤ := ⌊(c + Real.pi) / (2 * Real.pi)⌋
  set c0 : ℝ := c - k * (2 * Real.pi)
  have hk1 : (k : ℝ) ≤ (c + Real.pi) / (2 * Real.pi) := Int.floor_le _
  have hk2 : (c + Real.pi) / (2 * Real.pi) < k + 1 := Int.lt_floor_add_one _
  have hpos : 0 < 2 * Real.pi := by linarith
  have a1 : (k : ℝ) * (2 * Real.pi) ≤ c + Real.pi := by rwa [le_div_iff₀ hpos] at hk1
  have a2 : c + Real.pi < ((k : ℝ) + 1) * (2 * Real.pi) := by rwa [div_lt_iff₀ hpos] at hk2
  have hc : c = c0 + k * (2 * Real.pi) := by simp [c0]
  have : volume (Set.Ico c (c + 2 * Real.pi) ∩ G) = volume (Set.Ico c0 (c0 + 2 * Real.pi) ∩ G) := by
    rw [← g55d_shift G hper k c0 (c0 + 2 * Real.pi), ← hc]
    congr 2; rw [hc]; ring
  rw [this, ← g55d_split G hper (-Real.pi) c0 (by simp only [c0]; linarith)
    (by simp only [c0]; linarith)]
  congr 2; ring

lemma g55d_clause2 {ι : Type*} [Fintype ι] [DecidableEq ι] (X : Mat ι) (a : ℝ) :
    width X = width (phase a • X) := by
  have hph : phase a ≠ 0 := by unfold phase; exact Complex.exp_ne_zero _
  have hW : 0 ∈ numericalRange X ↔ 0 ∈ numericalRange (phase a • X) := by
    constructor
    · rintro ⟨R, hR, h0⟩; exact ⟨R, hR, by rw [Matrix.mul_smul, Matrix.trace_smul, h0, smul_zero]⟩
    · rintro ⟨R, hR, h0⟩
      refine ⟨R, hR, ?_⟩
      rw [Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul] at h0
      exact (mul_eq_zero.mp h0).resolve_left hph
  set G : Set ℝ := {s | (hermitianReal (phase s • X)).PosSemidef}
  have hper : ∀ (s : ℝ) (k : ℤ), s + k * (2 * Real.pi) ∈ G ↔ s ∈ G := by
    intro s k
    have : phase (s + k * (2 * Real.pi)) = phase s := by
      unfold phase
      rw [show ((s + k * (2 * Real.pi) : ℝ) : ℂ) * Complex.I =
        (s : ℂ) * Complex.I + (k : ℂ) * (2 * Real.pi * Complex.I) by push_cast; ring,
        Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
    simp only [G, Set.mem_ofPred_eq, this]
  have h1 : gammaSet X = Set.Ico (-Real.pi) Real.pi ∩ G := by
    ext t; simp only [gammaSet, G, Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_Ico]; tauto
  have h2 : gammaSet (phase a • X) =
      (fun t => t + a) ⁻¹' (Set.Ico (-Real.pi + a) (-Real.pi + a + 2 * Real.pi) ∩ G) := by
    ext t
    simp only [gammaSet, G, Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_Ico, Set.mem_preimage,
      smul_smul, g55d_phase_mul]
    constructor
    · rintro ⟨b1, b2, b3⟩; exact ⟨⟨by linarith, by linarith⟩, b3⟩
    · rintro ⟨⟨b1, b2⟩, b3⟩; exact ⟨by linarith, by linarith, b3⟩
  have hL : gammaLength (phase a • X) = gammaLength X := by
    unfold gammaLength
    rw [h2, measure_preimage_add_right, g55d_Jconst G hper, h1]
  unfold width
  rw [hL]
  simp only [hW]
/-- the sphere parametrising the PSD pairs -/
def g55d_sph (ι : Type*) [Fintype ι] : Set (Mat ι × Mat ι) :=
  {BC | ∑ i, ∑ j, Complex.normSq (BC.1 i j) + ∑ i, ∑ j, Complex.normSq (BC.2 i j) = 1}

lemma g55d_trace_cm {ι : Type*} [Fintype ι] (B : Mat ι) :
    (Bᴴ * B).trace = ((∑ i, ∑ j, Complex.normSq (B i j) : ℝ) : ℂ) := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply]
  push_cast
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [Complex.normSq_eq_conj_mul_self]; rfl

lemma g55d_sph_compact (ι : Type*) [Fintype ι] : IsCompact (g55d_sph ι) := by
  have hK : IsCompact ((Set.univ.pi fun _ : ι => Set.univ.pi fun _ : ι => Metric.closedBall (0 : ℂ) 1)
      ×ˢ (Set.univ.pi fun _ : ι => Set.univ.pi fun _ : ι => Metric.closedBall (0 : ℂ) 1)) :=
    (isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_closedBall _ _).prod
      (isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_closedBall _ _)
  refine hK.of_isClosed_subset ?_ ?_
  · refine isClosed_eq ?_ continuous_const
    fun_prop
  · intro BC hBC
    have hBC' : ∑ i, ∑ j, Complex.normSq (BC.1 i j) + ∑ i, ∑ j, Complex.normSq (BC.2 i j) = 1 :=
      hBC
    have hnn : ∀ (M : Mat ι), 0 ≤ ∑ i, ∑ j, Complex.normSq (M i j) := fun M =>
      Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => Complex.normSq_nonneg _
    have hle : ∀ (M : Mat ι) (i j : ι), Complex.normSq (M i j) ≤ ∑ i, ∑ j, Complex.normSq (M i j) :=
      fun M i j => (Finset.single_le_sum (f := fun j => Complex.normSq (M i j))
        (fun j _ => Complex.normSq_nonneg _) (Finset.mem_univ j)).trans
        (Finset.single_le_sum (f := fun i => ∑ j, Complex.normSq (M i j))
          (fun i _ => Finset.sum_nonneg fun j _ => Complex.normSq_nonneg _) (Finset.mem_univ i))
    have hb : ∀ (M : Mat ι) (i j : ι), ∑ i, ∑ j, Complex.normSq (M i j) ≤ 1 →
        M i j ∈ Metric.closedBall (0 : ℂ) 1 := by
      intro M i j h
      rw [Metric.mem_closedBall, dist_zero_right]
      have h1 := (hle M i j).trans h
      rw [Complex.normSq_eq_norm_sq] at h1
      nlinarith [norm_nonneg (M i j)]
    refine ⟨fun i _ j _ => hb _ i j ?_, fun i _ j _ => hb _ i j ?_⟩
    · linarith [hnn BC.2, hBC']
    · linarith [hnn BC.1, hBC']

lemma g55d_omega_eq {ι : Type*} [Fintype ι] (a : ℝ) (ha : 0 ≤ a) (hap : a < Real.pi) :
    omega (ι := ι) a = (fun BC : Mat ι × Mat ι => blend a (BC.1ᴴ * BC.1) (BC.2ᴴ * BC.2)) ''
      g55d_sph ι := by
  ext R
  constructor
  · rintro ⟨-, -, P, Q, hP, hQ, htr, rfl⟩
    open scoped MatrixOrder in
    obtain ⟨B, hB⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hP.nonneg
    open scoped MatrixOrder in
    obtain ⟨C, hC⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hQ.nonneg
    have hB' : P = Bᴴ * B := hB
    have hC' : Q = Cᴴ * C := hC
    refine ⟨(B, C), ?_, ?_⟩
    · simp only [g55d_sph, Set.mem_setOf_eq]
      rw [hB', hC', g55d_trace_cm, g55d_trace_cm] at htr
      exact_mod_cast htr
    · simp only [hB', hC']
  · rintro ⟨⟨B, C⟩, hBC, rfl⟩
    refine ⟨ha, hap, Bᴴ * B, Cᴴ * C, Matrix.posSemidef_conjTranspose_mul_self B,
      Matrix.posSemidef_conjTranspose_mul_self C, ?_, rfl⟩
    rw [g55d_trace_cm, g55d_trace_cm]
    simp only [g55d_sph, Set.mem_setOf_eq] at hBC
    exact_mod_cast hBC

lemma g55d_omega_compact {ι : Type*} [Fintype ι] (a : ℝ) (ha : 0 ≤ a) (hap : a < Real.pi) :
    IsCompact (omega (ι := ι) a) := by
  rw [g55d_omega_eq a ha hap]
  refine (g55d_sph_compact ι).image ?_
  unfold blend
  fun_prop

lemma g55d_omega_nonempty {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (a : ℝ) (ha : 0 ≤ a) (hap : a < Real.pi) : (omega (ι := ι) a).Nonempty := by
  refine ⟨blend a (((Fintype.card ι : ℂ))⁻¹ • 1) 0, ha, hap, _, 0, ?_, Matrix.PosSemidef.zero, ?_, rfl⟩
  · refine Matrix.PosSemidef.one.smul ?_
    have : (0 : ℝ) ≤ ((Fintype.card ι : ℝ))⁻¹ := by positivity
    have e : ((((Fintype.card ι : ℝ))⁻¹ : ℝ) : ℂ) = ((Fintype.card ι : ℂ))⁻¹ := by push_cast; rfl
    rw [← e]; exact Complex.zero_le_real.mpr this
  · rw [Matrix.trace_smul, Matrix.trace_one, Matrix.trace_zero, add_zero, smul_eq_mul]
    have : (Fintype.card ι : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
    field_simp

lemma g55d_omega_convex {ι : Type*} [Fintype ι] (a : ℝ) : Convex ℝ (omega (ι := ι) a) := by
  rintro _ ⟨ha, hap, P1, Q1, hP1, hQ1, h1, rfl⟩ _ ⟨-, -, P2, Q2, hP2, hQ2, h2, rfl⟩ s t hs ht hst
  have hs' : (0 : ℂ) ≤ (s : ℂ) := Complex.zero_le_real.mpr hs
  have ht' : (0 : ℂ) ≤ (t : ℂ) := Complex.zero_le_real.mpr ht
  refine ⟨ha, hap, (s : ℂ) • P1 + (t : ℂ) • P2, (s : ℂ) • Q1 + (t : ℂ) • Q2,
    (hP1.smul hs').add (hP2.smul ht'), (hQ1.smul hs').add (hQ2.smul ht'), ?_, ?_⟩
  · simp only [Matrix.trace_add, Matrix.trace_smul, smul_eq_mul]
    have : (s : ℂ) * (P1.trace + Q1.trace) + (t : ℂ) * (P2.trace + Q2.trace) = 1 := by
      have : (s : ℂ) + t = 1 := by exact_mod_cast hst
      rw [h1, h2]; linear_combination this
    linear_combination this
  · unfold blend
    simp only [smul_add, smul_smul, ← Complex.coe_smul]
    ext i j
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    ring


lemma g55d_clause1 {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι] (X : Mat ι)
    (h : 0 ∉ numericalRange X) :
    X ≠ 0 ∧ width X = closedWidth X ∧ width X < Real.pi := by
  have hp := Real.pi_pos
  have hD' : ∀ R ∈ omega (ι := ι) 0, IsDensityMatrix R := by
    rintro _ ⟨-, -, P, Q, hP, hQ, htr, rfl⟩
    have e : blend 0 P Q = P + Q := by simp [blend, phase]
    rw [e]; exact ⟨hP.add hQ, by rw [Matrix.trace_add]; exact htr⟩
  have hK := g55d_omega_compact (ι := ι) 0 le_rfl hp
  have hne := g55d_omega_nonempty (ι := ι) 0 le_rfl hp
  have hX0 : X ≠ 0 := by
    rintro rfl; apply h
    obtain ⟨R, hR⟩ := hne
    exact ⟨R, hD' R hR, by simp⟩
  refine ⟨hX0, by unfold width closedWidth; rw [if_neg h], ?_⟩
  unfold width; rw [if_neg h]
  suffices 0 < gammaLength X by linarith
  let f : Mat ι → ℂ := fun R => (R * X).trace
  have hf : Continuous f := by
    show Continuous fun R : Mat ι => (R * X).trace
    fun_prop
  obtain ⟨R0, hR0, hmin⟩ := hK.exists_isMinOn hne (continuous_norm.comp hf).continuousOn
  obtain ⟨R1, hR1, hmax⟩ := hK.exists_isMaxOn hne (continuous_norm.comp hf).continuousOn
  set z0 := f R0 with hz0def
  set M := ‖f R1‖
  have hz0 : z0 ≠ 0 := fun h0 => h ⟨R0, hD' R0 hR0, h0⟩
  have hz0pos : 0 < ‖z0‖ := norm_pos_iff.mpr hz0
  have hM : ∀ R ∈ omega (ι := ι) 0, ‖f R‖ ≤ M := fun R hR => isMaxOn_iff.mp hmax R hR
  have hMpos : 0 < M := lt_of_lt_of_le hz0pos (hM R0 hR0)
  have hkey : ∀ R ∈ omega (ι := ι) 0, ‖z0‖ ^ 2 ≤ (conj z0 * f R).re := by
    intro R hR
    set w := f R - z0 with hw
    set A := (conj z0 * w).re
    set B := Complex.normSq w
    have hB : 0 ≤ B := Complex.normSq_nonneg w
    have hs : ∀ s : ℝ, 0 < s → s ≤ 1 → 0 ≤ 2 * A + s * B := by
      intro s hs0 hs1
      have hRs : (1 - s) • R0 + s • R ∈ omega (ι := ι) 0 :=
        g55d_omega_convex 0 hR0 hR (by linarith) hs0.le (by ring)
      have h1 := isMinOn_iff.mp hmin _ hRs
      have hfs : f ((1 - s) • R0 + s • R) = z0 + (s : ℂ) * w := by
        simp only [f, hw, hz0def, Matrix.add_mul, Matrix.smul_mul, Matrix.trace_add,
          Matrix.trace_smul, Complex.real_smul]
        push_cast; ring
      simp only [Function.comp, hfs] at h1
      have h2 : ‖z0‖ ^ 2 ≤ ‖z0 + (s : ℂ) * w‖ ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
      rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq, Complex.normSq_add,
        Complex.normSq_mul, Complex.normSq_ofReal] at h2
      have e : (z0 * conj ((s : ℂ) * w)).re = s * A := by
        simp only [A, map_mul, Complex.conj_ofReal]
        rw [show z0 * ((s : ℂ) * conj w) = (s : ℂ) * (z0 * conj w) by ring, Complex.re_ofReal_mul]
        congr 1
        rw [← Complex.conj_re (conj z0 * w)]; simp [mul_comm]
      rw [e] at h2
      have : 0 ≤ s * (2 * A + s * B) := by nlinarith
      exact (mul_nonneg_iff_of_pos_left hs0).mp this
    have hA : 0 ≤ A := by
      by_contra hA; rw [not_le] at hA
      rcases hB.lt_or_eq with hB' | hB'
      · have hsp : 0 < min 1 (-A / B) := lt_min one_pos (div_pos (by linarith) hB')
        have := hs (min 1 (-A / B)) hsp (min_le_left _ _)
        have h3 : min 1 (-A / B) * B ≤ -A := by
          calc min 1 (-A / B) * B ≤ (-A / B) * B := by
                gcongr; exact min_le_right _ _
            _ = -A := by field_simp
        linarith
      · have := hs 1 one_pos le_rfl; rw [← hB'] at this; linarith
    have e : conj z0 * f R = conj z0 * z0 + conj z0 * w := by rw [hw]; ring
    rw [e, Complex.add_re, Complex.conj_mul', ← Complex.ofReal_pow, Complex.ofReal_re]
    linarith
  set θ0 := Complex.arg (conj z0)
  have hθ : phase θ0 * (‖z0‖ : ℂ) = conj z0 := by
    have := Complex.norm_mul_exp_arg_mul_I (conj z0)
    rw [Complex.norm_conj] at this
    unfold phase; rw [mul_comm]; exact this
  have hph : Continuous phase := by unfold phase; fun_prop
  obtain ⟨δ, hδ, hδc⟩ := Metric.continuous_iff.mp hph θ0 (‖z0‖ / M) (div_pos hz0pos hMpos)
  have hsub : Set.Ioo (max (θ0 - δ) (-Real.pi)) θ0 ⊆ gammaSet X := by
    intro t ht
    obtain ⟨ht1, ht2⟩ := ht
    have ht1a := (max_lt_iff.mp ht1).1
    have ht1b := (max_lt_iff.mp ht1).2
    refine ⟨ht1b.le, lt_of_lt_of_le ht2 (Complex.arg_le_pi _), ?_⟩
    rw [← g55d_K1]
    intro R hR
    have hRo : R ∈ omega (ι := ι) 0 := ⟨le_rfl, hp, R, 0, hR.1, Matrix.PosSemidef.zero,
      by rw [Matrix.trace_zero, add_zero]; exact hR.2, by simp [blend, phase]⟩
    have hd : dist (phase t) (phase θ0) < ‖z0‖ / M := hδc t (by
      rw [Real.dist_eq, abs_lt]; constructor <;> linarith)
    rw [dist_eq_norm] at hd
    have e : (R * (phase t • X)).trace = phase θ0 * f R + (phase t - phase θ0) * f R := by
      simp only [f, Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul]; ring
    rw [e, Complex.add_re]
    have h1 : ‖z0‖ ≤ (phase θ0 * f R).re := by
      have := hkey R hRo
      rw [← hθ] at this
      have e2 : (phase θ0 * (‖z0‖ : ℂ) * f R).re = ‖z0‖ * (phase θ0 * f R).re := by
        rw [show phase θ0 * (‖z0‖ : ℂ) * f R = (‖z0‖ : ℂ) * (phase θ0 * f R) by ring,
          Complex.re_ofReal_mul]
      rw [e2] at this
      nlinarith
    have h2 : -((‖z0‖ / M) * M) ≤ ((phase t - phase θ0) * f R).re := by
      have := Complex.abs_re_le_norm ((phase t - phase θ0) * f R)
      rw [norm_mul] at this
      have h3 : ‖phase t - phase θ0‖ * ‖f R‖ ≤ (‖z0‖ / M) * M :=
        mul_le_mul hd.le (hM R hRo) (norm_nonneg _) (div_pos hz0pos hMpos).le
      have := (abs_le.mp this).1
      linarith
    rw [div_mul_cancel₀ _ hMpos.ne'] at h2
    linarith
  have hsup : gammaSet X ⊆ Set.Ico (-Real.pi) Real.pi := fun t ht => ⟨ht.1, ht.2.1⟩
  have hfin : volume (gammaSet X) ≠ ⊤ :=
    ne_top_of_le_ne_top (by simp) (measure_mono hsup)
  have hle := ENNReal.toReal_mono hfin (measure_mono hsub)
  have hlt : max (θ0 - δ) (-Real.pi) < θ0 :=
    max_lt (by linarith) (Complex.neg_pi_lt_arg _)
  rw [Real.volume_Ioo, ENNReal.toReal_ofReal (by linarith)] at hle
  unfold gammaLength
  linarith

theorem solution {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι] (X : Mat ι) :
    (0 ∉ numericalRange X → X ≠ 0 ∧ width X = closedWidth X ∧ width X < Real.pi) ∧
    (∀ a : ℝ, width X = width (phase a • X)) ∧
    (∀ G : Mat ι, IsUnit G.det → width X = width (G * X * Gᴴ)) ∧
    ((∀ z ∈ numericalRange X, 0 ≤ z.re) ↔ (hermitianReal X).PosSemidef) ∧
    (X ≠ 0 → closedWidth X < Real.pi → X.trace ≠ 0) := by
  refine ⟨g55d_clause1 X, fun a => g55d_clause2 X a, fun G hG => g55d_clause3 X G hG, g55d_clause4 X, g55d_clause5 X⟩
