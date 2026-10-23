-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Frontier30.P13.valueUpperBound
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T13:29:14.144979+00:00
-- url     : https://prove2.me/submissions/8a892032-5bb3-467d-9b7c-756a6beb25b9

import Definitions.Def_QAlgorithms_Papers_Independent_Frontier30_P13

noncomputable section

open Filter

open QAlgorithms.Papers.Independent.Dependency50.P10 (complexify physicalCovariance)

open scoped ComplexOrder

attribute [local instance] Classical.decEq

attribute [local instance] Classical.propDecidable

namespace QAlgorithms.Papers.Independent.Frontier30.P13

open Matrix

theorem x8_fb_psd {α β 𝕜 : Type*} [RCLike 𝕜] [Fintype α] [Fintype β] {A : Matrix α α 𝕜}
    {B : Matrix β β 𝕜} (hA : A.PosSemidef) (hB : B.PosSemidef) : (fromBlocks A 0 0 B).PosSemidef := by
  rw [posSemidef_iff_dotProduct_mulVec] at hA hB ⊢
  refine ⟨?_, fun x => ?_⟩
  · rw [IsHermitian, fromBlocks_conjTranspose, hA.1.eq, hB.1.eq]; simp
  · rw [fromBlocks_mulVec]
    have h1 := hA.2 (x ∘ Sum.inl)
    have h2 := hB.2 (x ∘ Sum.inr)
    simp only [zero_mulVec, add_zero, zero_add] at *
    simp only [dotProduct, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, Pi.star_apply] at *
    exact add_nonneg h1 h2

theorem x8_psd_of_eq {n R : Type*} [Ring R] [PartialOrder R] [StarRing R] {M N : Matrix n n R}
    (h : M.PosSemidef) (e : M = N) : N.PosSemidef := e ▸ h

/-! complexify -/

section cx
variable {n m k : Type*}

theorem x8_cx_mul [Fintype m] (X : Matrix n m ℝ) (Y : Matrix m k ℝ) :
    complexify (X * Y) = complexify X * complexify Y := by
  ext i j; simp [complexify, mul_apply]

theorem x8_cx_sub (X Y : Matrix n m ℝ) : complexify (X - Y) = complexify X - complexify Y := by
  ext i j; simp [complexify]

theorem x8_cx_add (X Y : Matrix n m ℝ) : complexify (X + Y) = complexify X + complexify Y := by
  ext i j; simp [complexify]

theorem x8_cx_smul (r : ℝ) (X : Matrix n m ℝ) : complexify (r • X) = (r : ℂ) • complexify X := by
  ext i j; simp [complexify]

theorem x8_cx_neg (X : Matrix n m ℝ) : complexify (-X) = -complexify X := by
  ext i j; simp [complexify]

theorem x8_cx_one [DecidableEq n] : complexify (1 : Matrix n n ℝ) = 1 := by
  ext i j; by_cases h : i = j <;> simp [complexify, one_apply, h]

theorem x8_cx_T (X : Matrix n m ℝ) : complexify Xᵀ = (complexify X)ᵀ := rfl

theorem x8_cx_H (X : Matrix n m ℝ) : (complexify X)ᴴ = complexify Xᵀ := by
  ext i j; simp [complexify]

theorem x8_cx_fb {p q : Type*} (X : Matrix n m ℝ) (Y : Matrix n q ℝ) (Z : Matrix p m ℝ)
    (W : Matrix p q ℝ) :
    complexify (fromBlocks X Y Z W) = fromBlocks (complexify X) (complexify Y) (complexify Z)
      (complexify W) := by
  ext (i | i) (j | j) <;> rfl

theorem x8_cx_zero : complexify (0 : Matrix n m ℝ) = 0 := by ext; simp [complexify]

end cx

/-- complexification of a real PSD matrix is PSD -/
theorem x8_cpsd {n : Type*} [Fintype n] {X : Matrix n n ℝ} (hX : X.PosSemidef) :
    (complexify X).PosSemidef := by
  rw [posSemidef_iff_dotProduct_mulVec] at hX ⊢
  refine ⟨?_, fun z => ?_⟩
  · rw [IsHermitian, x8_cx_H, ← conjTranspose_eq_transpose_of_trivial, hX.1.eq]
  · have h1 := hX.2 (fun i => (z i).re)
    have h2 := hX.2 (fun i => (z i).im)
    have hsym : ∀ i j, X i j = X j i := fun i j => by
      have := congrFun (congrFun hX.1.eq j) i
      simpa [conjTranspose_apply] using this
    rw [Complex.nonneg_iff]
    simp only [dotProduct, mulVec, complexify, Pi.star_apply, Finset.mul_sum, Complex.re_sum,
      Complex.im_sum] at h1 h2 ⊢
    simp only [star_trivial, Complex.star_def, Complex.mul_re, Complex.mul_im, Complex.conj_re,
      Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im] at h1 h2 ⊢
    constructor
    · have := add_nonneg h1 h2
      refine le_of_le_of_eq this ?_
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      ring
    · have : ∑ i, ∑ j, (z i).re * X i j * (z j).im = ∑ i, ∑ j, (z i).im * X i j * (z j).re := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
        rw [hsym]; ring
      have e2 : ∑ i, ∑ j, ((z i).re * (X i j * (z j).im + 0 * (z j).re) +
          -(z i).im * (X i j * (z j).re - 0 * (z j).im)) =
          ∑ i, ∑ j, (z i).re * X i j * (z j).im - ∑ i, ∑ j, (z i).im * X i j * (z j).re := by
        rw [← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun j _ => ?_
        ring
      rw [e2, this, sub_self]

/-! the symplectic form -/

theorem x8_J_apply {A : Type*} (i j : ModeQuadrature A) : phaseJ A i j =
    if i.1 = j.1 then (if i.2 = j.2 then 0 else if i.2 then 1 else -1) else 0 := rfl

theorem x8_J_sq (A : Type*) [Fintype A] : phaseJ A * phaseJ A = -1 := by
  ext i j
  rw [neg_apply, one_apply, mul_apply]
  obtain ⟨a, q⟩ := i; obtain ⟨a', q'⟩ := j
  simp only [x8_J_apply, Fintype.sum_prod_type, Fintype.sum_bool]
  by_cases h : a = a'
  · subst h; cases q <;> cases q' <;> simp
  · have : ((a, q) : A × Bool) ≠ (a', q') := by simp [h]
    rw [if_neg this, neg_zero]
    refine Finset.sum_eq_zero fun x _ => ?_
    rcases eq_or_ne x a' with rfl | hx
    · simp [h]
    · simp [hx]

theorem x8_J_T (A : Type*) [Fintype A] : (phaseJ A)ᵀ = -phaseJ A := by
  ext i j
  rw [neg_apply, transpose_apply]
  obtain ⟨a, q⟩ := i; obtain ⟨a', q'⟩ := j
  simp only [x8_J_apply]
  by_cases h : a = a'
  · subst h; cases q <;> cases q' <;> simp
  · simp [h, Ne.symm h]

theorem x8_R_sq (A : Type*) [Fintype A] : reversal A * reversal A = 1 := by
  ext ⟨a, q⟩ ⟨a', q'⟩
  simp only [reversal, diagonal_mul_diagonal]
  by_cases h : (a, q) = (a', q')
  · rw [h]; cases q' <;> simp
  · simp [diagonal_apply_ne _ h, one_apply_ne h]

theorem x8_RJR (A : Type*) [Fintype A] : reversal A * phaseJ A * reversal A = -phaseJ A := by
  ext i j
  rw [neg_apply]
  simp only [reversal, diagonal_mul, mul_diagonal]
  obtain ⟨a, q⟩ := i; obtain ⟨a', q'⟩ := j
  simp only [x8_J_apply]
  by_cases h : a = a'
  · subst h; cases q <;> cases q' <;> simp
  · simp [h]

theorem x8_bJ_sq (A B : Type*) [Fintype A] [Fintype B] : bipJ A B * bipJ A B = -1 := by
  rw [bipJ, fromBlocks_multiply, x8_J_sq, x8_J_sq, ← fromBlocks_one, fromBlocks_neg]
  simp

theorem x8_bJ_T (A B : Type*) [Fintype A] [Fintype B] : (bipJ A B)ᵀ = -bipJ A B := by
  rw [bipJ, fromBlocks_transpose, x8_J_T, x8_J_T, fromBlocks_neg]
  simp

section phys
variable {n : Type*} [Fintype n]

theorem x8_cJ_sq {J : Matrix n n ℝ} (hJ2 : J * J = -1) :
    complexify J * complexify J = -1 := by
  rw [← x8_cx_mul, hJ2, x8_cx_neg, x8_cx_one]

theorem x8_phys_T {F J : Matrix n n ℝ} (h : physicalCovariance F J) (hJ : Jᵀ = -J) :
    (complexify F + Complex.I • complexify J).PosSemidef := by
  refine x8_psd_of_eq h.2.transpose ?_
  rw [transpose_sub, transpose_smul, ← x8_cx_T, ← x8_cx_T, h.1, hJ, x8_cx_neg, smul_neg,
    sub_neg_eq_add]

theorem x8_re_nonneg {z : ℂ} (h : 0 ≤ z) : z = (z.re : ℂ) ∧ 0 ≤ z.re := by
  obtain ⟨h1, h2⟩ := Complex.nonneg_iff.1 h
  exact ⟨Complex.ext (by simp) (by simp [h2.symm]), h1⟩

theorem x8_phys_pd {F J : Matrix n n ℝ} (h : physicalCovariance F J) (hJ : Jᵀ = -J)
    (hJ2 : J * J = -1) {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s < 1) :
    (complexify F - ((s : ℂ) * Complex.I) • complexify J).PosDef := by
  set H1 := complexify F - Complex.I • complexify J with hH1
  set H2 := complexify F + Complex.I • complexify J with hH2
  have h1 : H1.PosSemidef := h.2
  have h2 : H2.PosSemidef := x8_phys_T h hJ
  have he : complexify F - ((s : ℂ) * Complex.I) • complexify J =
      (((1 + s) / 2 : ℝ) : ℂ) • H1 + (((1 - s) / 2 : ℝ) : ℂ) • H2 := by
    ext i j
    simp only [hH1, hH2, Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    push_cast; ring
  have ha : (0 : ℝ) < (1 + s) / 2 := by linarith
  have hb : (0 : ℝ) < (1 - s) / 2 := by linarith
  have hpsd : (complexify F - ((s : ℂ) * Complex.I) • complexify J).PosSemidef := by
    rw [he]
    exact (h1.smul (by exact_mod_cast ha.le)).add (h2.smul (by exact_mod_cast hb.le))
  refine PosDef.of_dotProduct_mulVec_pos hpsd.1 fun x hx => ?_
  refine lt_of_le_of_ne (hpsd.dotProduct_mulVec_nonneg x) fun h0 => hx ?_
  rw [he] at h0
  simp only [add_mulVec, smul_mulVec, dotProduct_add, dotProduct_smul, smul_eq_mul] at h0
  obtain ⟨e1, r1⟩ := x8_re_nonneg (h1.dotProduct_mulVec_nonneg x)
  obtain ⟨e2, r2⟩ := x8_re_nonneg (h2.dotProduct_mulVec_nonneg x)
  have hre := congrArg Complex.re h0
  simp only [Complex.zero_re, Complex.add_re, Complex.re_ofReal_mul] at hre
  have z1 : (star x ⬝ᵥ (H1 *ᵥ x)).re = 0 := by nlinarith
  have z2 : (star x ⬝ᵥ (H2 *ᵥ x)).re = 0 := by nlinarith
  have k1 : H1 *ᵥ x = 0 := (h1.dotProduct_mulVec_zero_iff x).1 (by rw [e1, z1]; simp)
  have k2 : H2 *ᵥ x = 0 := (h2.dotProduct_mulVec_zero_iff x).1 (by rw [e2, z2]; simp)
  have k3 : complexify J *ᵥ x = 0 := by
    have : (H2 - H1) *ᵥ x = 0 := by rw [sub_mulVec, k1, k2, sub_zero]
    have e : H2 - H1 = (2 * Complex.I) • complexify J := by
      rw [hH1, hH2]; ext i j; simp [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply]; ring
    rw [e, smul_mulVec] at this
    exact (smul_eq_zero.1 this).resolve_left (by simp)
  have : complexify J *ᵥ (complexify J *ᵥ x) = -x := by
    rw [mulVec_mulVec, x8_cJ_sq hJ2, neg_mulVec, one_mulVec]
  rw [k3, mulVec_zero] at this
  exact neg_eq_zero.1 this.symm

end phys

section bip
variable {A B : Type*} [Fintype A] [Fintype B]

theorem x8_R_T : (reversal A)ᵀ = reversal A := by
  simp [reversal, diagonal_transpose]

theorem x8_L_T : (fromBlocks (reversal A) 0 0 (1 : Matrix (ModeQuadrature B) (ModeQuadrature B) ℝ))ᵀ =
    fromBlocks (reversal A) 0 0 1 := by
  rw [fromBlocks_transpose, x8_R_T]; simp

theorem x8_L_sq : fromBlocks (reversal A) 0 0 (1 : Matrix (ModeQuadrature B) (ModeQuadrature B) ℝ) *
    fromBlocks (reversal A) 0 0 1 = 1 := by
  rw [fromBlocks_multiply, x8_R_sq, ← fromBlocks_one]; simp

theorem x8_Fp_phys {GA : Matrix (ModeQuadrature A) (ModeQuadrature A) ℝ}
    {GB : Matrix (ModeQuadrature B) (ModeQuadrature B) ℝ}
    (hA : physicalCovariance GA (phaseJ A)) (hB : physicalCovariance GB (phaseJ B)) :
    physicalCovariance (fromBlocks (reversal A * GA * reversal A) 0 0 GB) (bipJ A B) := by
  refine ⟨?_, ?_⟩
  · rw [fromBlocks_transpose, transpose_mul, transpose_mul, x8_R_T, hA.1, hB.1, ← Matrix.mul_assoc]
    simp
  · have e : complexify (fromBlocks (reversal A * GA * reversal A) 0 0 GB) -
        Complex.I • complexify (bipJ A B) =
        fromBlocks ((complexify (reversal A))ᴴ * (complexify GA + Complex.I • complexify (phaseJ A)) *
          complexify (reversal A)) 0 0 (complexify GB - Complex.I • complexify (phaseJ B)) := by
      rw [bipJ, x8_cx_fb, x8_cx_fb, x8_cx_zero, fromBlocks_smul, sub_eq_add_neg, fromBlocks_neg,
        fromBlocks_add]
      congr 1
      · rw [x8_cx_H, x8_R_T, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul,
          ← x8_cx_mul, ← x8_cx_mul, ← x8_cx_mul, ← x8_cx_mul, x8_RJR, x8_cx_neg, smul_neg]
      all_goals simp [x8_cx_zero]
    rw [e]
    exact x8_fb_psd ((x8_phys_T hA (x8_J_T A)).conjTranspose_mul_mul_same _) hB.2

theorem x8_below {G : Matrix (BipPhase A B) (BipPhase A B) ℝ} {p t : ℝ} (hp : feasibleScale G p)
    (ht : t ∈ symplecticSpectrum (partialTransposeCM G) (bipJ A B)) : p ≤ t := by
  by_contra hlt'
  have hlt := not_le.1 hlt'
  obtain ⟨ht0, hdet⟩ := ht
  obtain ⟨hp0, -, GA, GB, hA, hB, hD⟩ := hp
  have hp0' : 0 < p := ht0.trans hlt
  set L := fromBlocks (reversal A) 0 0 (1 : Matrix (ModeQuadrature B) (ModeQuadrature B) ℝ) with hL
  set F' := fromBlocks (reversal A * GA * reversal A) 0 0 GB with hF'
  have hM : partialTransposeCM G = L * G * L := rfl
  have hLF : L * fromBlocks GA 0 0 GB * L = F' := by
    rw [hL, hF', fromBlocks_multiply, fromBlocks_multiply]; simp
  have hD' : (L * (G - p • fromBlocks GA 0 0 GB) * L).PosSemidef := by
    have := hD.conjTranspose_mul_mul_same L
    rwa [conjTranspose_eq_transpose_of_trivial, hL, x8_L_T, ← hL] at this
  have hD'e : L * (G - p • fromBlocks GA 0 0 GB) * L = partialTransposeCM G - p • F' := by
    rw [hM, ← hLF, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul]
  rw [hD'e] at hD'
  have hpd := ((x8_phys_pd (x8_Fp_phys hA hB) (x8_bJ_T A B) (by convert x8_bJ_sq A B)
    (s := t / p) (div_nonneg ht0.le hp0) ((div_lt_one hp0').2 hlt)).smul
    (a := (p : ℂ)) (by exact_mod_cast hp0'))
  have hsum := PosDef.posSemidef_add (x8_cpsd hD') hpd
  have e : complexify (partialTransposeCM G - p • F') + (p : ℂ) • (complexify F' -
      (((t / p : ℝ) : ℂ) * Complex.I) • complexify (bipJ A B)) =
      complexify (partialTransposeCM G) - ((t : ℂ) * Complex.I) • complexify (bipJ A B) := by
    rw [x8_cx_sub, x8_cx_smul, smul_sub, smul_smul]
    have : (p : ℂ) * (((t / p : ℝ) : ℂ) * Complex.I) = (t : ℂ) * Complex.I := by
      push_cast; field_simp
    rw [this]; abel
  rw [e] at hsum
  letI : DecidableEq (BipPhase A B) := Classical.decEq _
  obtain ⟨v, hv, hMv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  have := hsum.dotProduct_mulVec_pos hv
  rw [hMv, dotProduct_zero] at this
  exact lt_irrefl _ this

theorem x8_cx_star {n : Type*} [Fintype n] (X : Matrix n n ℝ) (v : n → ℂ) :
    complexify X *ᵥ star v = star (complexify X *ᵥ v) := by
  ext i
  simp [mulVec, dotProduct, complexify, star_sum, mul_comm]

theorem x8_form_anti {n : Type*} [Fintype n] {J : Matrix n n ℝ} (hJ : Jᵀ = -J) (v : n → ℂ) :
    star (star v ⬝ᵥ (complexify J *ᵥ v)) = -(star v ⬝ᵥ (complexify J *ᵥ v)) := by
  have hJ' : ∀ i j, J j i = -J i j := fun i j => by
    have := congrFun (congrFun hJ i) j; simpa using this
  simp only [dotProduct, mulVec, complexify, star_sum, Finset.mul_sum, Pi.star_apply, star_mul',
    star_star, Complex.star_def, Complex.conj_ofReal, ← Finset.sum_neg_distrib]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [hJ' j i]; push_cast; rw [Complex.conj_conj]; ring

theorem x8_exists_root [Nonempty A] {G : Matrix (BipPhase A B) (BipPhase A B) ℝ}
    (hG : physicalCovariance G (bipJ A B)) :
    (symplecticSpectrum (partialTransposeCM G) (bipJ A B)).Nonempty := by
  letI : DecidableEq (BipPhase A B) := Classical.decEq _
  set L := fromBlocks (reversal A) 0 0 (1 : Matrix (ModeQuadrature B) (ModeQuadrature B) ℝ) with hL
  have hM : partialTransposeCM G = L * G * L := rfl
  have hJT := x8_bJ_T A B
  have hJ2 : bipJ A B * bipJ A B = -1 := by convert x8_bJ_sq A B
  have hGpd : (complexify G).PosDef := by
    have := x8_phys_pd hG hJT hJ2 (s := 0) le_rfl one_pos
    simpa using this
  have hLL : complexify L * complexify L = 1 := by
    rw [← x8_cx_mul, hL, x8_L_sq]; ext i j; by_cases h : i = j <;> simp [complexify, one_apply, h]
  have hMpd : (complexify (partialTransposeCM G)).PosDef := by
    have := hGpd.conjTranspose_mul_mul_same (B := complexify L) (fun v w h => by
      have := congrArg (fun u => complexify L *ᵥ u) h
      simpa [mulVec_mulVec, hLL] using this)
    rwa [x8_cx_H, hL, x8_L_T, ← hL, ← x8_cx_mul, ← x8_cx_mul, ← hM] at this
  set cJ := complexify (bipJ A B) with hcJ
  set cM := complexify (partialTransposeCM G) with hcM
  set X : Matrix (BipPhase A B) (BipPhase A B) ℂ := -(cJ * cM) with hX
  haveI : Nonempty (BipPhase A B) := ⟨Sum.inl (Classical.arbitrary A, false)⟩
  obtain ⟨μ, hμ⟩ := spectrum.nonempty_of_isAlgClosed_of_finiteDimensional ℂ X
  rw [spectrum.mem_iff, Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero, not_not] at hμ
  obtain ⟨v, hv, hXv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hμ
  have hXv' : X *ᵥ v = μ • v := by
    rw [Algebra.algebraMap_eq_smul_one, sub_mulVec, smul_mulVec, one_mulVec, sub_eq_zero] at hXv
    exact hXv.symm
  have hMv : cM *ᵥ v = μ • (cJ *ᵥ v) := by
    have : cJ *ᵥ (X *ᵥ v) = cM *ᵥ v := by
      rw [mulVec_mulVec, hX, Matrix.mul_neg, ← Matrix.mul_assoc, x8_cJ_sq hJ2, neg_mul, neg_neg,
        Matrix.one_mul]
    rw [← this, hXv', mulVec_smul]
  have ha : 0 < star v ⬝ᵥ (cM *ᵥ v) := hMpd.dotProduct_mulVec_pos hv
  have hab : star v ⬝ᵥ (cM *ᵥ v) = μ * (star v ⬝ᵥ (cJ *ᵥ v)) := by
    rw [hMv, dotProduct_smul, smul_eq_mul]
  have hb : star (star v ⬝ᵥ (cJ *ᵥ v)) = -(star v ⬝ᵥ (cJ *ᵥ v)) := x8_form_anti hJT v
  obtain ⟨hare, -⟩ := x8_re_nonneg ha.le
  have ha0 : star v ⬝ᵥ (cM *ᵥ v) ≠ 0 := ne_of_gt ha
  have hb0 : star v ⬝ᵥ (cJ *ᵥ v) ≠ 0 := by
    intro h; rw [h, mul_zero] at hab; exact ha0 hab
  have hsa : star (star v ⬝ᵥ (cM *ᵥ v)) = star v ⬝ᵥ (cM *ᵥ v) := by
    rw [hare]; simp
  have hμre : μ.re = 0 := by
    have h1 : star (star v ⬝ᵥ (cM *ᵥ v)) = star μ * star (star v ⬝ᵥ (cJ *ᵥ v)) := by
      rw [hab, star_mul']
    rw [hsa, hb, hab] at h1
    have h2 : (μ + star μ) * (star v ⬝ᵥ (cJ *ᵥ v)) = 0 := by linear_combination h1
    have h3 := congrArg Complex.re ((mul_eq_zero.1 h2).resolve_right hb0)
    simp at h3; linarith
  have hμe : μ = (μ.im : ℂ) * Complex.I := by
    apply Complex.ext <;> simp [hμre]
  have hτ : μ.im ≠ 0 := by
    intro h; rw [h] at hμe; simp at hμe; rw [hμe, zero_mul] at hab; exact ha0 hab
  rcases lt_or_gt_of_ne hτ with hneg | hpos
  · refine ⟨-μ.im, by linarith, ?_⟩
    apply Matrix.exists_mulVec_eq_zero_iff.mp
    refine ⟨star v, fun h => hv (by simpa using congrArg star h), ?_⟩
    rw [sub_mulVec, smul_mulVec, x8_cx_star, x8_cx_star, hMv, star_smul]
    have : star μ = ((-μ.im : ℝ) : ℂ) * Complex.I := by
      conv_lhs => rw [hμe]
      simp [Complex.ext_iff]
    rw [this, sub_self]
  · refine ⟨μ.im, hpos, ?_⟩
    apply Matrix.exists_mulVec_eq_zero_iff.mp
    refine ⟨v, hv, ?_⟩
    rw [sub_mulVec, smul_mulVec, hMv, ← hμe, sub_self]

theorem x8_main [Nonempty A] [Nonempty B] (G : Matrix (BipPhase A B) (BipPhase A B) ℝ)
    (hG : physicalCovariance G (bipJ A B)) : valueV G ≤ min (lambdaMin G) 1 := by
  by_cases hne : {p | feasibleScale G p}.Nonempty
  · refine le_min (csSup_le hne fun p hp => ?_) (csSup_le hne fun p hp => hp.2.1)
    unfold lambdaMin
    exact le_csInf (x8_exists_root hG) fun t ht => x8_below hp ht
  · rw [Set.not_nonempty_iff_eq_empty] at hne
    unfold valueV; rw [hne, Real.sSup_empty]
    exact le_min (Real.sInf_nonneg fun t ht => ht.1.le) zero_le_one

end bip

end QAlgorithms.Papers.Independent.Frontier30.P13

open QAlgorithms.Papers.Independent.Frontier30.P13 in
theorem solution {A B : Type*} [Fintype A] [Fintype B]
    [Nonempty A] [Nonempty B]
    (G : Matrix (BipPhase A B) (BipPhase A B) ℝ)
    (hG : physicalCovariance G (bipJ A B)) :
    valueV G ≤ min (lambdaMin G) 1 :=
  x8_main G hG
