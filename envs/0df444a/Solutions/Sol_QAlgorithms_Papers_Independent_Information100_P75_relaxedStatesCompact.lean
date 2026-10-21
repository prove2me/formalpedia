-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Information100.P75.relaxedStatesCompact
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-20T07:30:14.823058+00:00
-- url     : https://prove2.me/submissions/66a98c18-5370-46ef-b80b-08401ccb991b

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P75

noncomputable section

open QAlgorithms QAlgorithms.Papers QAlgorithms.Papers.Independent QAlgorithms.Papers.Independent.Information100 QAlgorithms.Papers.Independent.Information100.P75

open Classical

open scoped ComplexConjugate ComplexOrder Matrix

open MeasureTheory

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

lemma g55d_trace_blend_re {ι : Type*} [Fintype ι] (a : ℝ) (P Q : Mat ι) (hP : P.PosSemidef)
    (hQ : Q.PosSemidef) (h1 : P.trace + Q.trace = 1) :
    (blend a P Q).trace.re = Real.cos (a / 2) := by
  have hP' := g55d_trace_real P hP
  have hQ' := g55d_trace_real Q hQ
  have hs : P.trace.re + Q.trace.re = 1 := by
    have := congrArg Complex.re h1; simpa using this
  unfold blend
  rw [Matrix.trace_add, Matrix.trace_smul, Matrix.trace_smul]
  simp only [Complex.add_re, smul_eq_mul, Complex.mul_re, g55d_phase_re, g55d_phase_im, hP'.2,
    hQ'.2, mul_zero, sub_zero]
  rw [show -a / 2 = -(a / 2) by ring, Real.cos_neg]
  rw [← mul_add, hs, mul_one]

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

lemma g55d_omega_prop {ι : Type*} [Fintype ι] (a : ℝ) (R : Mat ι) (hR : R ∈ omega (ι := ι) a) :
    R ≠ 0 ∧ closedWidth R ≤ a := by
  obtain ⟨ha, hap, P, Q, hP, hQ, htr, rfl⟩ := hR
  have hp := Real.pi_pos
  constructor
  · intro h0
    have := g55d_trace_blend_re a P Q hP hQ htr
    rw [h0, Matrix.trace_zero, Complex.zero_re] at this
    have : 0 < Real.cos (a / 2) := Real.cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩
    linarith
  · have hsub : Set.Icc (-(Real.pi - a) / 2) ((Real.pi - a) / 2) ⊆ gammaSet (blend a P Q) := by
      intro t ht
      obtain ⟨ht1, ht2⟩ := ht
      refine ⟨by linarith, by linarith, ?_⟩
      rw [g55d_herm_phase_blend a t P Q hP.1 hQ.1]
      have c1 : 0 ≤ Real.cos (t + a / 2) :=
        Real.cos_nonneg_of_mem_Icc ⟨by linarith, by linarith⟩
      have c2 : 0 ≤ Real.cos (t - a / 2) :=
        Real.cos_nonneg_of_mem_Icc ⟨by linarith, by linarith⟩
      exact (hP.smul (Complex.zero_le_real.mpr c1)).add (hQ.smul (Complex.zero_le_real.mpr c2))
    have hsup : gammaSet (blend a P Q) ⊆ Set.Ico (-Real.pi) Real.pi := fun t ht => ⟨ht.1, ht.2.1⟩
    have hfin : volume (gammaSet (blend a P Q)) ≠ ⊤ :=
      ne_top_of_le_ne_top (by simp) (measure_mono hsup)
    have hle := ENNReal.toReal_mono hfin (measure_mono hsub)
    rw [Real.volume_Icc, ENNReal.toReal_ofReal (by linarith)] at hle
    unfold closedWidth gammaLength
    linarith

theorem solution {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (a : ℝ) (ha : 0 ≤ a) (hap : a < Real.pi) :
    (omega (ι := ι) a).Nonempty ∧ Convex ℝ (omega (ι := ι) a) ∧
    IsCompact (omega (ι := ι) a) ∧
    ∀ R ∈ omega (ι := ι) a, R ≠ 0 ∧ closedWidth R ≤ a :=
  ⟨g55d_omega_nonempty a ha hap, g55d_omega_convex a, g55d_omega_compact a ha hap,
    fun R hR => g55d_omega_prop a R hR⟩
