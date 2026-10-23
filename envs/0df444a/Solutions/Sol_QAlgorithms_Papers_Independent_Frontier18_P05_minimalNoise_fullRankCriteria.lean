-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Frontier18.P05.minimalNoise_fullRankCriteria
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T07:25:22.101944+00:00
-- url     : https://prove2.me/submissions/d6c378c7-36f7-4339-b896-7ce774b969ab

import Definitions.Def_QAlgorithms_Papers_Independent_Frontier18_P05

noncomputable section

open scoped ComplexOrder
open Matrix QAlgorithms.Papers.Independent.Dependency50.P10
  QAlgorithms.Papers.Independent.Frontier18.P05

namespace X5KernelRank

variable {a : Type*} [Fintype a] [DecidableEq a]

/-- The real projection matrix acts as the orthogonal projection onto the range. -/
lemma proj_mulVec (A : Matrix a a ℝ) (v : a → ℝ) :
    realRangeProjection A *ᵥ v =
      WithLp.ofLp ((LinearMap.range (Matrix.toEuclideanLin A)).starProjection
        (WithLp.toLp 2 v)) := by
  set U := LinearMap.range (Matrix.toEuclideanLin A)
  have hlin : (Matrix.toLin' (realRangeProjection A)) =
      (WithLp.linearEquiv 2 ℝ (a → ℝ)).toLinearMap ∘ₗ
        (U.starProjection : EuclideanSpace ℝ a →ₗ[ℝ] EuclideanSpace ℝ a) ∘ₗ
          (WithLp.linearEquiv 2 ℝ (a → ℝ)).symm.toLinearMap := by
    refine LinearMap.pi_ext' fun j => LinearMap.ext_ring ?_
    funext i
    simp [Matrix.toLin'_apply, realRangeProjection, Matrix.mulVec_single_one,
      EuclideanSpace.single]
    rfl
  have := congrArg (fun f => f v) hlin
  simpa [Matrix.toLin'_apply] using this

section real
variable (A : Matrix a a ℝ)

lemma toLp_mulVec_mem (v : a → ℝ) :
    WithLp.toLp 2 (A *ᵥ v) ∈ LinearMap.range (Matrix.toEuclideanLin A) :=
  ⟨WithLp.toLp 2 v, rfl⟩

lemma proj_idem (v : a → ℝ) :
    realRangeProjection A *ᵥ (realRangeProjection A *ᵥ v) = realRangeProjection A *ᵥ v := by
  rw [proj_mulVec, proj_mulVec, WithLp.toLp_ofLp,
    Submodule.starProjection_eq_self_iff.2 (Submodule.starProjection_apply_mem _ _)]

lemma proj_A (v : a → ℝ) : realRangeProjection A *ᵥ (A *ᵥ v) = A *ᵥ v := by
  rw [proj_mulVec, Submodule.starProjection_eq_self_iff.2 (toLp_mulVec_mem A v)]

lemma mem_orth_iff (hA : Aᵀ = A) (w : EuclideanSpace ℝ a) :
    w ∈ (LinearMap.range (Matrix.toEuclideanLin A))ᗮ ↔ A *ᵥ WithLp.ofLp w = 0 := by
  rw [LinearMap.orthogonal_range, ← Matrix.toEuclideanLin_conjTranspose_eq_adjoint,
    conjTranspose_eq_transpose_of_trivial, hA, LinearMap.mem_ker]
  constructor
  · intro h; have := congrArg WithLp.ofLp h; simpa using this
  · intro h; apply_fun WithLp.ofLp using WithLp.ofLp_injective 2; simpa using h

lemma A_proj (hA : Aᵀ = A) (v : a → ℝ) : A *ᵥ (realRangeProjection A *ᵥ v) = A *ᵥ v := by
  set U := LinearMap.range (Matrix.toEuclideanLin A)
  have hmem : WithLp.toLp 2 v - U.starProjection (WithLp.toLp 2 v) ∈ Uᗮ :=
    Submodule.sub_starProjection_mem_orthogonal _
  rw [mem_orth_iff A hA] at hmem
  rw [proj_mulVec]
  have : A *ᵥ (v - WithLp.ofLp (U.starProjection (WithLp.toLp 2 v))) = 0 := by simpa using hmem
  rw [Matrix.mulVec_sub, sub_eq_zero] at this
  exact this.symm

lemma proj_ker (hA : Aᵀ = A) (v : a → ℝ) (h : A *ᵥ v = 0) : realRangeProjection A *ᵥ v = 0 := by
  rw [proj_mulVec, (Submodule.starProjection_apply_eq_zero_iff _).2 ((mem_orth_iff A hA _).2 h)]
  rfl

lemma mat_ext {M N : Matrix a a ℝ} (h : ∀ v, M *ᵥ v = N *ᵥ v) : M = N :=
  Matrix.toLin'.injective (LinearMap.ext fun v => by simpa [Matrix.toLin'_apply] using h v)

lemma B_unit (hA : Aᵀ = A) : IsUnit (A + (1 - realRangeProjection A)) := by
  rw [← Matrix.mulVec_injective_iff_isUnit]
  intro v w hvw
  rw [← sub_eq_zero] at hvw ⊢
  rw [← Matrix.mulVec_sub] at hvw
  set u := v - w
  have h1 := congrArg (realRangeProjection A *ᵥ ·) hvw
  simp only [Matrix.add_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.mulVec_add,
    Matrix.mulVec_sub, proj_A, proj_idem, Matrix.mulVec_zero] at h1
  have hAu : A *ᵥ u = 0 := by simpa using h1
  have hPu := proj_ker A hA u hAu
  simpa [Matrix.add_mulVec, Matrix.sub_mulVec, hAu, hPu] using hvw

lemma B_mulVec_proj (hA : Aᵀ = A) (x : a → ℝ) :
    (A + (1 - realRangeProjection A)) *ᵥ (realRangeProjection A *ᵥ x) = A *ᵥ x := by
  rw [Matrix.add_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec, A_proj A hA, proj_idem, sub_self,
    add_zero]

lemma proj_B_mulVec (z : a → ℝ) :
    realRangeProjection A *ᵥ ((A + (1 - realRangeProjection A)) *ᵥ z) = A *ᵥ z := by
  rw [Matrix.add_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.mulVec_add,
    Matrix.mulVec_sub, proj_A, proj_idem, sub_self, add_zero]

lemma supportInverse_mulVec (x : a → ℝ) :
    supportInverse A *ᵥ x = realRangeProjection A *ᵥ
      ((A + (1 - realRangeProjection A))⁻¹ *ᵥ (realRangeProjection A *ᵥ x)) := by
  simp [supportInverse, Matrix.mulVec_mulVec, Matrix.mul_assoc]

lemma S1 (hA : Aᵀ = A) (x : a → ℝ) :
    A *ᵥ (supportInverse A *ᵥ x) = realRangeProjection A *ᵥ x := by
  have hB := B_unit A hA
  have hdet := (Matrix.isUnit_iff_isUnit_det _).1 hB
  rw [supportInverse_mulVec, A_proj A hA]
  set y := realRangeProjection A *ᵥ x
  have hz : (A + (1 - realRangeProjection A)) *ᵥ
      ((A + (1 - realRangeProjection A))⁻¹ *ᵥ y) = y := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hdet, Matrix.one_mulVec]
  have := congrArg (realRangeProjection A *ᵥ ·) hz
  simp only [proj_B_mulVec] at this
  rw [this]
  exact proj_idem A x

lemma S2 (hA : Aᵀ = A) (x : a → ℝ) :
    supportInverse A *ᵥ (A *ᵥ x) = realRangeProjection A *ᵥ x := by
  have hB := B_unit A hA
  have hdet := (Matrix.isUnit_iff_isUnit_det _).1 hB
  have hQB : ∀ y, (A + (1 - realRangeProjection A))⁻¹ *ᵥ
      ((A + (1 - realRangeProjection A)) *ᵥ y) = y := fun y => by
    rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hdet, Matrix.one_mulVec]
  rw [supportInverse_mulVec, proj_A, ← B_mulVec_proj A hA, hQB, proj_idem]

lemma S3 (x : a → ℝ) :
    realRangeProjection A *ᵥ (supportInverse A *ᵥ x) = supportInverse A *ᵥ x := by
  rw [supportInverse_mulVec, proj_idem]

lemma S4 (x : a → ℝ) :
    supportInverse A *ᵥ (realRangeProjection A *ᵥ x) = supportInverse A *ᵥ x := by
  rw [supportInverse_mulVec, supportInverse_mulVec, proj_idem]

lemma M_AAp (hA : Aᵀ = A) : A * supportInverse A = realRangeProjection A :=
  mat_ext fun v => by rw [← Matrix.mulVec_mulVec, S1 A hA]
lemma M_ApA (hA : Aᵀ = A) : supportInverse A * A = realRangeProjection A :=
  mat_ext fun v => by rw [← Matrix.mulVec_mulVec, S2 A hA]
lemma M_PAp : realRangeProjection A * supportInverse A = supportInverse A :=
  mat_ext fun v => by rw [← Matrix.mulVec_mulVec, S3]
lemma M_ApP : supportInverse A * realRangeProjection A = supportInverse A :=
  mat_ext fun v => by rw [← Matrix.mulVec_mulVec, S4]
lemma M_AP (hA : Aᵀ = A) : A * realRangeProjection A = A :=
  mat_ext fun v => by rw [← Matrix.mulVec_mulVec, A_proj A hA]
lemma M_PA : realRangeProjection A * A = A :=
  mat_ext fun v => by rw [← Matrix.mulVec_mulVec, proj_A]
lemma M_PP : realRangeProjection A * realRangeProjection A = realRangeProjection A :=
  mat_ext fun v => by rw [← Matrix.mulVec_mulVec, proj_idem]

lemma M_SP (hA : Aᵀ = A) (S : Matrix a a ℝ) (hker : ∀ w, A *ᵥ w = 0 → S *ᵥ w = 0) :
    S * realRangeProjection A = S :=
  mat_ext fun v => by
    rw [← Matrix.mulVec_mulVec]
    have h : A *ᵥ (v - realRangeProjection A *ᵥ v) = 0 := by
      rw [Matrix.mulVec_sub, A_proj A hA, sub_self]
    have := hker _ h
    rw [Matrix.mulVec_sub, sub_eq_zero] at this
    exact this.symm

lemma M_PS (hA : Aᵀ = A) (S : Matrix a a ℝ) (hSt : Sᵀ = -S)
    (hker : ∀ w, A *ᵥ w = 0 → S *ᵥ w = 0) :
    realRangeProjection A * S = S :=
  mat_ext fun v => by
    rw [← Matrix.mulVec_mulVec, proj_mulVec]
    set U := LinearMap.range (Matrix.toEuclideanLin A)
    have hmem : WithLp.toLp 2 (S *ᵥ v) ∈ U := by
      rw [← Submodule.orthogonal_orthogonal U, Submodule.mem_orthogonal]
      intro w hw
      rw [mem_orth_iff A hA] at hw
      have h0 := hker _ hw
      have : WithLp.ofLp w ⬝ᵥ (S *ᵥ v) = 0 := by
        rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hSt, Matrix.neg_mulVec, h0,
          neg_zero, zero_dotProduct]
      simpa [PiLp.inner_apply, dotProduct, mul_comm] using this
    rw [Submodule.starProjection_eq_self_iff.2 hmem]

end real

section cx

lemma cx_mul {b c d : Type*} [Fintype c] (A : Matrix b c ℝ) (B : Matrix c d ℝ) :
    complexify (A * B) = complexify A * complexify B := by
  ext i j; simp [complexify, Matrix.mul_apply]

lemma cx_sub {b c : Type*} (A B : Matrix b c ℝ) :
    complexify (A - B) = complexify A - complexify B := by
  ext i j; simp [complexify]

lemma cx_transpose {b c : Type*} (A : Matrix b c ℝ) :
    complexify Aᵀ = (complexify A)ᵀ := by
  ext i j; simp [complexify]

lemma cx_neg {b c : Type*} (A : Matrix b c ℝ) : complexify (-A) = -complexify A := by
  ext i j; simp [complexify]

lemma cx_mulVec (A : Matrix a a ℝ) (v : a → ℝ) :
    complexify A *ᵥ (fun i => (v i : ℂ)) = fun i => ((A *ᵥ v) i : ℂ) := by
  funext i; simp [complexify, Matrix.mulVec, dotProduct]

lemma mem_cker {M : Matrix a a ℂ} {v : a → ℂ} : v ∈ complexKernel M ↔ M *ᵥ v = 0 := by
  simp [complexKernel]

lemma rank_add_finrank_ker (M : Matrix a a ℂ) :
    M.rank + Module.finrank ℂ (complexKernel M) = Fintype.card a := by
  have := LinearMap.finrank_range_add_finrank_ker M.mulVecLin
  rw [Module.finrank_fintype_fun_eq_card] at this
  exact this

end cx

open scoped InnerProductSpace in
lemma even_finrank_range_of_skew {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (T : E →ₗ[ℝ] E) (hT : LinearMap.adjoint T = -T) :
    Even (Module.finrank ℝ (LinearMap.range T)) := by
  set W := LinearMap.range T
  let T' : W →ₗ[ℝ] W := T.restrict (fun x _ => LinearMap.mem_range_self T x)
  have hT'apply : ∀ w : W, (T' w : E) = T w := fun w => rfl
  have hadj : -T' = LinearMap.adjoint T' := by
    rw [LinearMap.eq_adjoint_iff]
    intro x y
    simp only [LinearMap.neg_apply, Submodule.coe_inner, hT'apply, inner_neg_left]
    rw [← LinearMap.adjoint_inner_left, hT, LinearMap.neg_apply, inner_neg_left]
  have hker : LinearMap.ker T' = ⊥ := by
    rw [eq_bot_iff]
    intro w hw
    rw [LinearMap.mem_ker] at hw
    have h1 : T w = 0 := by rw [← hT'apply, hw]; rfl
    have h2 : (w : E) ∈ Wᗮ := by
      rw [LinearMap.orthogonal_range, hT, LinearMap.mem_ker, LinearMap.neg_apply, h1, neg_zero]
    have h3 : (w : E) = 0 := by
      have := Submodule.inner_right_of_mem_orthogonal w.2 h2
      exact inner_self_eq_zero.1 this
    rw [Submodule.mem_bot]
    exact Subtype.ext h3
  have hdet : LinearMap.det T' ≠ 0 := by
    intro h
    exact (LinearMap.det_eq_zero_iff_ker_ne_bot.1 h) hker
  let b := stdOrthonormalBasis ℝ W
  have hdadj : LinearMap.det (LinearMap.adjoint T') = LinearMap.det T' := by
    rw [← LinearMap.det_toMatrix b.toBasis, ← LinearMap.det_toMatrix b.toBasis,
      LinearMap.toMatrix_adjoint, Matrix.det_conjTranspose]
    simp
  have hneg : LinearMap.det (-T') = (-1) ^ Module.finrank ℝ W * LinearMap.det T' := by
    rw [← neg_one_smul ℝ T', LinearMap.det_smul]
  rw [← hadj, hneg] at hdadj
  have : ((-1 : ℝ)) ^ Module.finrank ℝ W = 1 := by
    have := mul_right_cancel₀ hdet (hdadj.trans (one_mul _).symm)
    exact this
  exact (neg_one_pow_eq_one_iff_even (by norm_num)).1 this

lemma proj_symm (A : Matrix a a ℝ) : (realRangeProjection A)ᵀ = realRangeProjection A := by
  ext i j
  simp only [Matrix.transpose_apply, realRangeProjection]
  have h := Submodule.inner_starProjection_left_eq_right
    (LinearMap.range (Matrix.toEuclideanLin A)) (EuclideanSpace.single i (1 : ℝ))
    (EuclideanSpace.single j (1 : ℝ))
  simpa [EuclideanSpace.inner_single_left, EuclideanSpace.inner_single_right] using h

lemma supportInverse_symm (A : Matrix a a ℝ) (hA : Aᵀ = A) :
    (supportInverse A)ᵀ = supportInverse A := by
  simp only [supportInverse, Matrix.transpose_mul, proj_symm, Matrix.transpose_nonsing_inv,
    Matrix.transpose_add, Matrix.transpose_sub, Matrix.transpose_one, hA, Matrix.mul_assoc]

lemma cx_conjTranspose' {b c : Type*} (A : Matrix b c ℝ) :
    (complexify A)ᴴ = complexify Aᵀ := by
  ext i j; simp [complexify, Matrix.conjTranspose_apply]

lemma cx_psd (M : Matrix a a ℝ) (h : M.PosSemidef) : (complexify M).PosSemidef := by
  have hMt : Mᵀ = M := by
    have := h.isHermitian
    rwa [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial] at this
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ fun v => ?_
  · rw [Matrix.IsHermitian, cx_conjTranspose', hMt]
  · set re : a → ℝ := fun i => (v i).re
    set im : a → ℝ := fun i => (v i).im
    have hre := h.dotProduct_mulVec_nonneg re
    have him := h.dotProduct_mulVec_nonneg im
    have key : star v ⬝ᵥ (complexify M *ᵥ v) =
        ((re ⬝ᵥ (M *ᵥ re) + im ⬝ᵥ (M *ᵥ im) : ℝ) : ℂ) := by
      have hsym : ∑ i, ∑ j, M i j * (re i * im j - im i * re j) = 0 := by
        have h1 : ∑ i, ∑ j, M i j * (im i * re j) = ∑ i, ∑ j, M i j * (re i * im j) := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
          have : M j i = M i j := by
            have := congrFun (congrFun hMt i) j
            simpa [Matrix.transpose_apply] using this
          rw [this]; ring
        simp only [mul_sub, Finset.sum_sub_distrib, h1, sub_self]
      apply Complex.ext
      · simp only [dotProduct, Matrix.mulVec, complexify, Pi.star_apply, Complex.re_sum,
          Finset.mul_sum, Complex.ofReal_re, star_trivial]
        simp [Complex.mul_re, Finset.mul_sum, Finset.sum_add_distrib, re, im, mul_comm,
          mul_left_comm, mul_assoc]
      · simp only [dotProduct, Matrix.mulVec, complexify, Pi.star_apply, Complex.im_sum,
          Finset.mul_sum, Complex.ofReal_im]
        simp only [Complex.mul_im, Complex.mul_re, Complex.star_def, Complex.conj_re,
          Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im, Complex.im_sum, Complex.re_sum,
          Finset.mul_sum]
        refine Eq.trans ?_ hsym
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
        simp only [re, im]
        ring
    rw [key]
    exact_mod_cast add_nonneg (by simpa using hre) (by simpa using him)

lemma cx_smul {b c : Type*} (r : ℝ) (A : Matrix b c ℝ) :
    complexify (r • A) = (r : ℂ) • complexify A := by
  ext i j; simp [complexify]

lemma cx_inj {b c : Type*} {A B : Matrix b c ℝ} (h : complexify A = complexify B) : A = B := by
  ext i j
  have := congrFun (congrFun h i) j
  simpa [complexify] using this

end X5KernelRank


open X5KernelRank in
theorem x5_supportInverseCriterion {n : ℕ} (hn : 0 < n)
    (X Y : Matrix (Phase n) (Phase n) ℝ) (hCP : (cpMatrix X Y).PosSemidef) :
    minimalNoise X Y ↔
      Y = commutatorDefect X * supportInverse Y * (commutatorDefect X).transpose := by
  set S := commutatorDefect X with hSdef
  set K := cpMatrix X Y with hKdef
  set Yc := complexify Y
  set Sc := complexify S
  -- antisymmetry of the commutator defect
  have hsig : (sigma n)ᵀ = -sigma n := by
    simp [sigma, Matrix.fromBlocks_transpose, Matrix.fromBlocks_neg]
  have hSt : Sᵀ = -S := by
    simp only [S, commutatorDefect, Matrix.transpose_sub, Matrix.transpose_mul,
      Matrix.transpose_transpose, hsig]
    simp only [Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_assoc]
    abel
  -- symmetry of `Y` from hermiticity of `K`
  have hYt : Yᵀ = Y := by
    ext i j
    have h := hCP.isHermitian.apply j i
    have h2 := congrArg Complex.re h
    simp [K, cpMatrix, complexify, Matrix.sub_apply] at h2
    simpa [Matrix.transpose_apply] using h2.symm
  have hKmv : ∀ v, K *ᵥ v = Yc *ᵥ v - Complex.I • (Sc *ᵥ v) := fun v => by
    simp [K, cpMatrix, Matrix.sub_mulVec, Matrix.smul_mulVec, Yc, Sc, S]
  have hKt : Kᵀ = Yc + Complex.I • Sc := by
    have : Scᵀ = -Sc := by simp only [Sc, ← cx_transpose, hSt, cx_neg]
    simp [K, cpMatrix, Matrix.transpose_sub, Matrix.transpose_smul, ← cx_transpose, hYt, Yc,
      this, Sc, S, sub_eq_add_neg]
  have hKtmv : ∀ v, Kᵀ *ᵥ v = Yc *ᵥ v + Complex.I • (Sc *ᵥ v) := fun v => by
    rw [hKt, Matrix.add_mulVec, Matrix.smul_mulVec]
  have hKtpsd : Kᵀ.PosSemidef := hCP.transpose
  -- kernel facts
  have kYK : ∀ v, Yc *ᵥ v = 0 → K *ᵥ v = 0 := by
    intro v hv
    have h1 := hCP.dotProduct_mulVec_nonneg v
    have h2 := hKtpsd.dotProduct_mulVec_nonneg v
    rw [hKmv, hv, zero_sub, dotProduct_neg] at h1
    rw [hKtmv, hv, zero_add] at h2
    have h3 : star v ⬝ᵥ (K *ᵥ v) = 0 := by
      rw [hKmv, hv, zero_sub, dotProduct_neg]
      exact le_antisymm (by simpa using h2) h1
    exact (hCP.dotProduct_mulVec_zero_iff v).1 h3
  have kYS : ∀ v, Yc *ᵥ v = 0 → Sc *ᵥ v = 0 := by
    intro v hv
    have := kYK v hv
    rw [hKmv, hv, zero_sub, neg_eq_zero, smul_eq_zero] at this
    exact this.resolve_left Complex.I_ne_zero
  have kSKY : ∀ v, Sc *ᵥ v = 0 → K *ᵥ v = 0 → Yc *ᵥ v = 0 := by
    intro v hs hk
    rw [hKmv, hs, smul_zero, sub_zero] at hk
    exact hk
  have part1 : complexKernel Sc ⊓ complexKernel K ≤ complexKernel Yc := fun v hv => by
    rw [Submodule.mem_inf, mem_cker, mem_cker] at hv
    exact mem_cker.2 (kSKY v hv.1 hv.2)
  have part2 : complexKernel Yc ≤ complexKernel K := fun v hv =>
    mem_cker.2 (kYK v (mem_cker.1 hv))
  have part3 : complexKernel Yc ≤ complexKernel Sc := fun v hv =>
    mem_cker.2 (kYS v (mem_cker.1 hv))
  -- real kernel inclusion
  have hkerR : ∀ w, Y *ᵥ w = 0 → S *ᵥ w = 0 := by
    intro w hw
    have h1 : Yc *ᵥ (fun i => (w i : ℂ)) = 0 := by
      rw [cx_mulVec, hw]; funext i; simp
    have h2 := kYS _ h1
    rw [cx_mulVec] at h2
    funext i
    have := congrFun h2 i
    simpa using this
  set P := realRangeProjection Y
  set Yp := supportInverse Y
  set Pc := complexify P
  set Ypc := complexify Yp
  have cYYp : Yc * Ypc = Pc := by rw [← cx_mul, M_AAp Y hYt]
  have cYpY : Ypc * Yc = Pc := by rw [← cx_mul, M_ApA Y hYt]
  have cPYp : Pc * Ypc = Ypc := by rw [← cx_mul, M_PAp]
  have cYP : Yc * Pc = Yc := by rw [← cx_mul, M_AP Y hYt]
  have cPP : Pc * Pc = Pc := by rw [← cx_mul, M_PP]
  have cSP : Sc * Pc = Sc := by rw [← cx_mul, M_SP Y hYt S hkerR]
  have cPS : Pc * Sc = Sc := by rw [← cx_mul, M_PS Y hYt S hSt hkerR]
  have mv : ∀ (M N : Matrix (Phase n) (Phase n) ℂ) (v : Phase n → ℂ), M *ᵥ (N *ᵥ v) = (M * N) *ᵥ v :=
    fun M N v => Matrix.mulVec_mulVec _ _ _
  set J : Matrix (Phase n) (Phase n) ℂ := Complex.I • (Ypc * Sc) with hJdef
  have hJmv : ∀ v, J *ᵥ v = Complex.I • (Ypc *ᵥ (Sc *ᵥ v)) := fun v => by
    rw [hJdef, Matrix.smul_mulVec, mv]
  have hPJ : ∀ v, Pc *ᵥ (J *ᵥ v) = J *ᵥ v := fun v => by
    rw [hJmv, Matrix.mulVec_smul, mv, cPYp]
  have hJP : ∀ v, J *ᵥ (Pc *ᵥ v) = J *ᵥ v := fun v => by
    rw [hJmv, hJmv, mv Sc Pc, cSP]
  have hYJ : ∀ v, Yc *ᵥ (J *ᵥ v) = Complex.I • (Sc *ᵥ v) := fun v => by
    rw [hJmv, Matrix.mulVec_smul, mv, mv, cYYp, cPS]
  have hYpY : ∀ v, Ypc *ᵥ (Yc *ᵥ v) = Pc *ᵥ v := fun v => by rw [mv, cYpY]
  have hYP : ∀ v, Yc *ᵥ (Pc *ᵥ v) = Yc *ᵥ v := fun v => by rw [mv, cYP]
  have hPP : ∀ v, Pc *ᵥ (Pc *ᵥ v) = Pc *ᵥ v := fun v => by rw [mv, cPP]
  have hYker : ∀ v, Yc *ᵥ v = 0 → Pc *ᵥ v = 0 := fun v hv => by
    rw [← hYpY, hv, Matrix.mulVec_zero]
  have hYsub : ∀ v, Yc *ᵥ (v - Pc *ᵥ v) = 0 := fun v => by
    rw [Matrix.mulVec_sub, hYP, sub_self]
  -- residual
  set R := rankResidual Y S with hRdef
  set Rc := complexify R
  have hRmv : ∀ v, Rc *ᵥ v = Yc *ᵥ v + Sc *ᵥ (Ypc *ᵥ (Sc *ᵥ v)) := fun v => by
    have : Rc = Yc - Sc * Ypc * (complexify S)ᵀ := by
      simp only [Rc, R, rankResidual, cx_sub, cx_mul, cx_transpose]; rfl
    rw [this, ← cx_transpose, hSt, cx_neg, Matrix.mul_neg, Matrix.sub_mulVec, Matrix.neg_mulVec,
      sub_neg_eq_add, ← mv, ← mv]
  -- subspaces
  set kY := complexKernel Yc
  set Ep := complexKernel (J - 1)
  set Em := complexKernel (J + 1)
  have memEp : ∀ v, v ∈ Ep ↔ J *ᵥ v = v := fun v => by
    rw [mem_cker, Matrix.sub_mulVec, Matrix.one_mulVec, sub_eq_zero]
  have memEm : ∀ v, v ∈ Em ↔ J *ᵥ v = -v := fun v => by
    rw [mem_cker, Matrix.add_mulVec, Matrix.one_mulVec, add_eq_zero_iff_eq_neg]
  have hPEp : ∀ v ∈ Ep, Pc *ᵥ v = v := fun v hv => by
    rw [memEp] at hv; rw [← hv, hPJ]
  have hPEm : ∀ v ∈ Em, Pc *ᵥ v = v := fun v hv => by
    rw [memEm] at hv
    have : v = -(J *ᵥ v) := by rw [hv, neg_neg]
    rw [this, Matrix.mulVec_neg, hPJ]
  -- Claim A
  have hA_sup : complexKernel K = kY ⊔ Ep := by
    apply le_antisymm
    · intro v hv
      rw [mem_cker] at hv
      have hsplit : v = (v - Pc *ᵥ v) + Pc *ᵥ v := by abel
      rw [hsplit]
      refine Submodule.add_mem_sup (mem_cker.2 (hYsub v)) ?_
      rw [memEp]
      have hK0 : K *ᵥ (Pc *ᵥ v) = 0 := by
        have h1 := kYK _ (hYsub v)
        rw [Matrix.mulVec_sub, hv, zero_sub, neg_eq_zero] at h1
        exact h1
      rw [hKmv, sub_eq_zero] at hK0
      rw [hJmv, ← Matrix.mulVec_smul, ← hK0, hYpY, hPP]
    · refine sup_le part2 fun v hv => ?_
      rw [memEp] at hv
      rw [mem_cker, hKmv]
      have := hYJ v
      rw [hv] at this
      rw [this, sub_self]
  have hA_inf : kY ⊓ Ep = ⊥ := by
    rw [eq_bot_iff]; intro v hv
    rw [Submodule.mem_inf] at hv
    have h1 := hYker v (mem_cker.1 hv.1)
    have h2 := (memEp v).1 hv.2
    rw [Submodule.mem_bot, ← h2, ← hJP, h1, Matrix.mulVec_zero]
  -- Claim B
  have hB_sup : complexKernel Kᵀ = kY ⊔ Em := by
    apply le_antisymm
    · intro v hv
      rw [mem_cker] at hv
      have hsplit : v = (v - Pc *ᵥ v) + Pc *ᵥ v := by abel
      rw [hsplit]
      refine Submodule.add_mem_sup (mem_cker.2 (hYsub v)) ?_
      rw [memEm]
      have hK0 : Kᵀ *ᵥ (Pc *ᵥ v) = 0 := by
        have h1 : Kᵀ *ᵥ (v - Pc *ᵥ v) = 0 := by
          rw [hKtmv, hYsub, kYS _ (hYsub v), smul_zero, add_zero]
        rw [Matrix.mulVec_sub, hv, zero_sub, neg_eq_zero] at h1
        exact h1
      rw [hKtmv, add_eq_zero_iff_eq_neg] at hK0
      rw [hJmv, ← Matrix.mulVec_smul, ← neg_neg (Complex.I • (Sc *ᵥ (Pc *ᵥ v))), ← hK0,
        Matrix.mulVec_neg, hYpY, hPP]
    · refine sup_le (fun v hv => ?_) fun v hv => ?_
      · have hv' := mem_cker.1 hv
        rw [mem_cker, hKtmv, hv', kYS v hv', smul_zero, add_zero]
      · rw [memEm] at hv
        rw [mem_cker, hKtmv]
        have := hYJ v
        rw [hv, Matrix.mulVec_neg] at this
        rw [← this, add_neg_cancel]
  have hB_inf : kY ⊓ Em = ⊥ := by
    rw [eq_bot_iff]; intro v hv
    rw [Submodule.mem_inf] at hv
    have h1 := hYker v (mem_cker.1 hv.1)
    rw [Submodule.mem_bot, ← hPEm v hv.2, h1]
  -- Claim C
  have hEpR : ∀ v ∈ Ep, Rc *ᵥ v = 0 := fun v hv => by
    rw [memEp] at hv
    have h1 : Ypc *ᵥ (Sc *ᵥ v) = (-Complex.I) • v := by
      have h0 := hJmv v
      rw [hv] at h0
      conv_rhs => rw [h0]
      rw [smul_smul]; simp
    have hY : Yc *ᵥ v = Complex.I • (Sc *ᵥ v) := by have := hYJ v; rwa [hv] at this
    rw [hRmv, h1, Matrix.mulVec_smul, hY, neg_smul, add_neg_cancel]
  have hEmR : ∀ v ∈ Em, Rc *ᵥ v = 0 := fun v hv => by
    rw [memEm] at hv
    have h1 : Ypc *ᵥ (Sc *ᵥ v) = Complex.I • v := by
      have : v = -(J *ᵥ v) := by rw [hv, neg_neg]
      conv_rhs => rw [this]
      rw [hJmv, smul_neg, smul_smul]; simp
    have hY : Yc *ᵥ v = -(Complex.I • (Sc *ᵥ v)) := by
      have := hYJ v
      rw [hv, Matrix.mulVec_neg] at this
      rw [← this, neg_neg]
    rw [hRmv, h1, Matrix.mulVec_smul, hY, neg_add_cancel]
  have hC_sup : complexKernel Rc = kY ⊔ (Ep ⊔ Em) := by
    apply le_antisymm
    · intro v hv
      rw [mem_cker] at hv
      have hsplit : v = (v - Pc *ᵥ v) + Pc *ᵥ v := by abel
      rw [hsplit]
      refine Submodule.add_mem_sup (mem_cker.2 (hYsub v)) ?_
      set u := Pc *ᵥ v
      have hRu : Rc *ᵥ u = 0 := by
        have h1 : Rc *ᵥ (v - u) = 0 := by rw [hRmv, hYsub, kYS _ (hYsub v)]; simp
        rw [Matrix.mulVec_sub, hv, zero_sub, neg_eq_zero] at h1
        exact h1
      have hJJ : J *ᵥ (J *ᵥ u) = u := by
        rw [hRmv] at hRu
        have h2 := congrArg (Ypc *ᵥ ·) hRu
        simp only [Matrix.mulVec_add, hYpY, Matrix.mulVec_zero] at h2
        rw [show Pc *ᵥ u = u from hPP v] at h2
        rw [hJmv, hJmv, Matrix.mulVec_smul, Matrix.mulVec_smul, smul_smul, Complex.I_mul_I,
          neg_one_smul, neg_eq_iff_eq_neg, ← add_eq_zero_iff_eq_neg, add_comm]
        exact h2
      have hsplit2 : u = (2 : ℂ)⁻¹ • (u + J *ᵥ u) + (2 : ℂ)⁻¹ • (u - J *ᵥ u) := by
        rw [← smul_add]; rw [show u + J *ᵥ u + (u - J *ᵥ u) = (2 : ℂ) • u by
          rw [two_smul]; abel]
        rw [smul_smul, inv_mul_cancel₀ two_ne_zero, one_smul]
      rw [hsplit2]
      refine Submodule.add_mem_sup ?_ ?_
      · refine Ep.smul_mem _ ((memEp _).2 ?_)
        rw [Matrix.mulVec_add, hJJ, add_comm]
      · refine Em.smul_mem _ ((memEm _).2 ?_)
        rw [Matrix.mulVec_sub, hJJ, neg_sub]
    · refine sup_le (fun v hv => ?_) (sup_le (fun v hv => mem_cker.2 (hEpR v hv))
        (fun v hv => mem_cker.2 (hEmR v hv)))
      have hv' := mem_cker.1 hv
      rw [mem_cker, hRmv, hv', kYS v hv']; simp
  have hFix : Ep ⊔ Em ≤ complexKernel (Pc - 1) := by
    refine sup_le (fun v hv => ?_) (fun v hv => ?_) <;>
      rw [mem_cker, Matrix.sub_mulVec, Matrix.one_mulVec, sub_eq_zero]
    · exact hPEp v hv
    · exact hPEm v hv
  have hC_inf : kY ⊓ (Ep ⊔ Em) = ⊥ := by
    rw [eq_bot_iff]; intro v hv
    rw [Submodule.mem_inf] at hv
    have h1 := hYker v (mem_cker.1 hv.1)
    have h2 := mem_cker.1 (hFix hv.2)
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, sub_eq_zero] at h2
    rw [Submodule.mem_bot, ← h2, h1]
  have hEE : Ep ⊓ Em = ⊥ := by
    rw [eq_bot_iff]; intro v hv
    rw [Submodule.mem_inf, memEp, memEm] at hv
    have : v = -v := hv.1.symm.trans hv.2
    rw [Submodule.mem_bot]
    have h2 : (2 : ℂ) • v = 0 := by rw [two_smul]; nth_rewrite 2 [this]; exact add_neg_cancel v
    exact (smul_eq_zero.1 h2).resolve_left two_ne_zero
  -- further identities
  have hYpT : Ypᵀ = Yp := supportInverse_symm Y hYt
  have cYpH : Ypcᴴ = Ypc := by rw [cx_conjTranspose', hYpT]
  have cScT : Scᵀ = -Sc := by rw [← cx_transpose, hSt, cx_neg]
  have cScH : Scᴴ = -Sc := by rw [cx_conjTranspose', hSt, cx_neg]
  have cPY : Pc * Yc = Yc := by rw [← cx_mul, M_PA]
  have cApP : Ypc * Pc = Ypc := by rw [← cx_mul, M_ApP]
  have hKH : Kᴴ = K := hCP.isHermitian.eq
  have hKmat : K = Yc - Complex.I • Sc := by simp [K, cpMatrix, Yc, Sc, S]
  have hRmat : Rc = Yc + Sc * Ypc * Sc := by
    have : Rc = Yc - Sc * Ypc * (complexify S)ᵀ := by
      simp only [Rc, R, rankResidual, cx_sub, cx_mul, cx_transpose]; rfl
    rw [this, ← cx_transpose, hSt, cx_neg, Matrix.mul_neg, sub_neg_eq_add]
  have half_nn : (0 : ℂ) ≤ 1 / 2 := by
    rw [show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by push_cast; ring]
    exact Complex.zero_le_real.2 (by norm_num)
  have hYcpsd : Yc.PosSemidef := by
    have h2 : K + Kᵀ = (2 : ℂ) • Yc := by rw [hKt, hKmat, two_smul]; abel
    have h3 := (hCP.add hKtpsd).smul half_nn
    rw [h2, smul_smul] at h3
    simpa using h3
  constructor
  · rintro ⟨-, hmin⟩
    set Z := Y - (1 / 2 : ℝ) • R with hZdef
    have hZc : complexify Z = Yc - (1 / 2 : ℂ) • Rc := by
      simp only [Z, cx_sub, cx_smul]; push_cast; rfl
    have r1 : ∀ M, Ypc * (Yc * M) = Pc * M := fun M => by rw [← Matrix.mul_assoc, cYpY]
    have r2 : ∀ M, Yc * (Ypc * M) = Pc * M := fun M => by rw [← Matrix.mul_assoc, cYYp]
    have r3 : ∀ M, Pc * (Yc * M) = Yc * M := fun M => by rw [← Matrix.mul_assoc, cPY]
    have r4 : ∀ M, Pc * (Sc * M) = Sc * M := fun M => by rw [← Matrix.mul_assoc, cPS]
    have r5 : ∀ M, Sc * (Pc * M) = Sc * M := fun M => by rw [← Matrix.mul_assoc, cSP]
    have r6 : ∀ M, Pc * (Ypc * M) = Ypc * M := fun M => by rw [← Matrix.mul_assoc, cPYp]
    have r7 : ∀ M, Ypc * (Pc * M) = Ypc * M := fun M => by rw [← Matrix.mul_assoc, cApP]
    have r8 : ∀ M, Yc * (Pc * M) = Yc * M := fun M => by rw [← Matrix.mul_assoc, cYP]
    have hZcp : (cpMatrix X Z).PosSemidef := by
      have e1 : cpMatrix X Z = (1 / 2 : ℂ) • ((Ypc * K)ᴴ * Yc * (Ypc * K)) := by
        rw [Matrix.conjTranspose_mul, hKH, cYpH]
        show complexify Z - Complex.I • Sc = _
        rw [hZc, hRmat, hKmat]
        simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.add_mul, Matrix.mul_add,
          Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_assoc, r1, r2, r3, r4, r5, r6, r7, r8, cYYp,
          cYpY, cPY, cPS, cSP, cPYp, cApP, cYP, smul_sub, smul_add, smul_smul]
        match_scalars
        all_goals (try rw [Complex.I_mul_I]); ring
      rw [e1]
      exact (hYcpsd.conjTranspose_mul_mul_same (Ypc * K)).smul half_nn
    have hRcpsd : Rc.PosSemidef := by
      set J' : Matrix (Phase n) (Phase n) ℂ := Complex.I • (Ypc * Sc) with hJ'
      have hJH : J'ᴴ = Complex.I • (Sc * Ypc) := by
        rw [hJ', Matrix.conjTranspose_smul, Matrix.conjTranspose_mul, cYpH, cScH]
        simp [Matrix.neg_mul]
      have hid : (2 : ℂ) • Rc = (1 + J')ᴴ * K * (1 + J') + (1 - J')ᴴ * Kᵀ * (1 - J') := by
        rw [Matrix.conjTranspose_add, Matrix.conjTranspose_sub, Matrix.conjTranspose_one, hJH, hKt,
          hKmat, hRmat, hJ']
        simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.add_mul, Matrix.mul_add, Matrix.one_mul,
          Matrix.mul_one, Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_assoc, r1, r2, r3, r4, r5,
          r6, r7, r8, cYYp, cYpY, cPY, cPS, cSP, cPYp, cApP, cYP, smul_sub, smul_add, smul_smul]
        match_scalars
        all_goals (try rw [Complex.I_mul_I]); ring
      have h1 := hCP.conjTranspose_mul_mul_same (1 + J')
      have h2 := hKtpsd.conjTranspose_mul_mul_same (1 - J')
      have h3 := (h1.add h2).smul half_nn
      rw [← hid, smul_smul] at h3
      simpa using h3
    have hRt : Rᵀ = R := by
      simp only [R, rankResidual, Matrix.transpose_sub, Matrix.transpose_mul,
        Matrix.transpose_transpose, hYt, supportInverse_symm Y hYt, Matrix.mul_assoc]
    have hRpsd : R.PosSemidef := by
      refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ fun x => ?_
      · rw [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial, hRt]
      · have h := hRcpsd.dotProduct_mulVec_nonneg (fun i => (x i : ℂ))
        have e : star (fun i => (x i : ℂ)) ⬝ᵥ (Rc *ᵥ fun i => (x i : ℂ)) =
            ((star x ⬝ᵥ (R *ᵥ x) : ℝ) : ℂ) := by
          rw [show Rc = complexify R from rfl, cx_mulVec]
          simp [dotProduct]
        rw [e] at h
        exact_mod_cast h
    have hYZ : (Y - Z).PosSemidef := by
      have : Y - Z = (1 / 2 : ℝ) • R := by simp [Z]
      rw [this]; exact hRpsd.smul (by norm_num)
    have hZY := hmin Z hZcp hYZ
    have h0 : (1 / 2 : ℝ) • R = 0 := by
      have : Y - Z = 0 := by rw [hZY, sub_self]
      simpa [Z] using this
    have hR0 : R = 0 := by
      rcases smul_eq_zero.1 h0 with h | h
      · norm_num at h
      · exact h
    exact sub_eq_zero.1 hR0
  · intro hYeq
    refine ⟨hCP, fun Z hZ hYZ => ?_⟩
    have hR0 : R = 0 := sub_eq_zero.2 hYeq
    have hRc0 : Rc = 0 := by
      ext i j; simp [Rc, hR0, complexify]
    have htop : complexKernel Rc = ⊤ := by
      rw [eq_top_iff]; intro v _; rw [mem_cker, hRc0, Matrix.zero_mulVec]
    set D := Y - Z with hDdef
    set Dc := complexify D
    set Zc := complexify Z
    have hZc : Zc = Yc - Dc := by
      simp only [Zc, Dc, D, cx_sub]; abel
    have hDc : Dc.PosSemidef := cx_psd D hYZ
    have hZ1 : (Zc - Complex.I • Sc).PosSemidef := hZ
    have hZt : Zᵀ = Z := by
      ext i j
      have h := hZ.isHermitian.apply j i
      have h2 := congrArg Complex.re h
      simp [cpMatrix, complexify, Matrix.sub_apply] at h2
      simpa [Matrix.transpose_apply] using h2.symm
    have hZ2 : (Zc + Complex.I • Sc).PosSemidef := by
      have := hZ1.transpose
      have e : (Zc - Complex.I • Sc)ᵀ = Zc + Complex.I • Sc := by
        rw [Matrix.transpose_sub, Matrix.transpose_smul, cScT, smul_neg, sub_neg_eq_add]
        congr 1
        show (complexify Z)ᵀ = complexify Z
        rw [← cx_transpose, hZt]
      rwa [e] at this
    have hZpsd : Zc.PosSemidef := by
      have h2 : (Zc - Complex.I • Sc) + (Zc + Complex.I • Sc) = (2 : ℂ) • Zc := by
        rw [two_smul]; abel
      have h3 := (hZ1.add hZ2).smul half_nn
      rw [h2, smul_smul] at h3
      simpa using h3
    -- every vector is killed by Dc
    have kill : ∀ v, star v ⬝ᵥ (Dc *ᵥ v) ≤ 0 → Dc *ᵥ v = 0 := fun v hv =>
      (hDc.dotProduct_mulVec_zero_iff v).1 (le_antisymm hv (hDc.dotProduct_mulVec_nonneg v))
    have hsub : kY ⊔ (Ep ⊔ Em) ≤ complexKernel Dc := by
      refine sup_le (fun v hv => ?_) (sup_le (fun v hv => ?_) (fun v hv => ?_))
      · have hYv := mem_cker.1 hv
        have h := hZpsd.dotProduct_mulVec_nonneg v
        rw [hZc, Matrix.sub_mulVec, hYv, zero_sub, dotProduct_neg, neg_nonneg] at h
        exact mem_cker.2 (kill v h)
      · have hKv : K *ᵥ v = 0 := mem_cker.1 (hA_sup ▸ (le_sup_right : Ep ≤ kY ⊔ Ep) hv)
        have h := hZ1.dotProduct_mulVec_nonneg v
        have e : Zc - Complex.I • Sc = K - Dc := by rw [hZc, hKmat]; abel
        rw [e, Matrix.sub_mulVec, hKv, zero_sub, dotProduct_neg, neg_nonneg] at h
        exact mem_cker.2 (kill v h)
      · have hKv : Kᵀ *ᵥ v = 0 := mem_cker.1 (hB_sup ▸ (le_sup_right : Em ≤ kY ⊔ Em) hv)
        have h := hZ2.dotProduct_mulVec_nonneg v
        have e : Zc + Complex.I • Sc = Kᵀ - Dc := by rw [hZc, hKt]; abel
        rw [e, Matrix.sub_mulVec, hKv, zero_sub, dotProduct_neg, neg_nonneg] at h
        exact mem_cker.2 (kill v h)
    have hDc0 : Dc = 0 := by
      ext i j
      have hv : (Pi.single j 1 : Phase n → ℂ) ∈ kY ⊔ (Ep ⊔ Em) := by
        rw [← hC_sup, htop]; trivial
      have := congrFun (mem_cker.1 (hsub hv)) i
      simpa [Matrix.mulVec_single_one] using this
    have hD0 : D = 0 := cx_inj (by
      rw [show complexify D = Dc from rfl, hDc0]; ext i j; simp [complexify])
    have : Y - Z = 0 := hD0
    exact (sub_eq_zero.1 this).symm

namespace X5FullRank

variable {a : Type*} [Fintype a] [DecidableEq a]

lemma rank_add_finrank_ker_real (M : Matrix a a ℝ) :
    M.rank + Module.finrank ℝ (LinearMap.ker M.mulVecLin) = Fintype.card a := by
  have := LinearMap.finrank_range_add_finrank_ker M.mulVecLin
  rw [Module.finrank_fintype_fun_eq_card] at this
  exact this

lemma det_ne_zero_of_rank (M : Matrix a a ℝ) (h : M.rank = Fintype.card a) : M.det ≠ 0 := by
  intro hdet
  obtain ⟨v, hv, hMv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  have hk := rank_add_finrank_ker_real M
  rw [h] at hk
  have h0 : Module.finrank ℝ (LinearMap.ker M.mulVecLin) = 0 := by omega
  rw [Submodule.finrank_eq_zero] at h0
  have : v ∈ LinearMap.ker M.mulVecLin := by simpa using hMv
  rw [h0] at this
  exact hv (by simpa using this)

lemma eq_zero_of_rank_zero (M : Matrix a a ℝ) (h : M.rank = 0) : M = 0 := by
  have h' : Module.finrank ℝ (LinearMap.range M.mulVecLin) = 0 := h
  rw [Submodule.finrank_eq_zero, LinearMap.range_eq_bot] at h'
  ext i j
  have := congrFun (LinearMap.congr_fun h' (Pi.single j 1)) i
  simpa [Matrix.mulVec_single_one] using this

lemma realRangeProjection_of_isUnit (M : Matrix a a ℝ) (h : IsUnit M) :
    realRangeProjection M = 1 := by
  have hr : LinearMap.range (Matrix.toEuclideanLin M) = ⊤ := by
    rw [LinearMap.range_eq_top]
    intro y
    obtain ⟨u, rfl⟩ := h
    refine ⟨WithLp.toLp 2 ((↑u⁻¹ : Matrix a a ℝ) *ᵥ WithLp.ofLp y), ?_⟩
    ext i
    simp [Matrix.toEuclideanLin, Matrix.mulVec_mulVec]
  ext i j
  simp only [realRangeProjection, hr, Submodule.starProjection_top]
  simp [Matrix.one_apply]

lemma supportInverse_of_isUnit (M : Matrix a a ℝ) (h : IsUnit M) :
    supportInverse M = M⁻¹ := by
  simp [supportInverse, realRangeProjection_of_isUnit M h]

/-- A real skew-symmetric matrix has nonnegative determinant. -/
lemma det_nonneg_of_skew (S : Matrix a a ℝ) (hS : Sᵀ = -S) : 0 ≤ S.det := by
  by_contra hneg
  push Not at hneg
  set φ : ℝ → ℝ := fun s => (s • S + (1 - s) • (1 : Matrix a a ℝ)).det with hφ
  have hcont : Continuous φ := by
    apply Continuous.matrix_det
    exact (continuous_id.smul continuous_const).add
      ((continuous_const.sub continuous_id).smul continuous_const)
  have h0 : φ 0 = 1 := by simp [φ]
  have h1 : φ 1 = S.det := by simp [φ]
  have hmem : (0 : ℝ) ∈ Set.Icc (φ 1) (φ 0) := by
    rw [h0, h1]; exact ⟨hneg.le, zero_le_one⟩
  obtain ⟨s, ⟨hs0, hs1⟩, hs⟩ :=
    intermediate_value_Icc' (zero_le_one' ℝ) hcont.continuousOn hmem
  have hs1' : s < 1 := by
    rcases lt_or_eq_of_le hs1 with h | h
    · exact h
    · exfalso; rw [h, h1] at hs; exact hneg.ne hs
  obtain ⟨v, hv, hMv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hs
  have hskew : v ⬝ᵥ (S *ᵥ v) = 0 := by
    have h2 : v ⬝ᵥ (S *ᵥ v) = (Sᵀ *ᵥ v) ⬝ᵥ v := by
      rw [Matrix.dotProduct_mulVec, Matrix.mulVec_transpose]
    rw [hS, Matrix.neg_mulVec, neg_dotProduct, dotProduct_comm (S *ᵥ v) v] at h2
    linarith
  have hq : v ⬝ᵥ ((s • S + (1 - s) • (1 : Matrix a a ℝ)) *ᵥ v) = 0 := by
    rw [hMv, dotProduct_zero]
  rw [Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
    dotProduct_add, dotProduct_smul, dotProduct_smul, hskew, smul_eq_mul, smul_eq_mul,
    mul_zero, zero_add] at hq
  have hvv : 0 < v ⬝ᵥ v := by
    have : 0 ≤ v ⬝ᵥ v := dotProduct_self_star_nonneg v
    rcases lt_or_eq_of_le this with h | h
    · exact h
    · exfalso; exact hv (dotProduct_self_eq_zero.mp h.symm)
  have : 0 < (1 - s) * (v ⬝ᵥ v) := mul_pos (by linarith) hvv
  linarith

lemma real_spectral (M : Matrix a a ℝ) (hM : M.IsHermitian) :
    ∃ U : Matrix a a ℝ, U * Uᵀ = 1 ∧ Uᵀ * U = 1 ∧
      M = U * diagonal hM.eigenvalues * Uᵀ := by
  have hst : ∀ X : Matrix a a ℝ, star X = Xᵀ := fun X => by
    rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial]
  refine ⟨(hM.eigenvectorUnitary : Matrix a a ℝ), ?_, ?_, ?_⟩
  · rw [← hst]; exact Unitary.coe_mul_star_self _
  · rw [← hst]; exact Unitary.coe_star_mul_self _
  · conv_lhs => rw [hM.spectral_theorem]
    rw [Unitary.conjStarAlgAut_apply, hst]
    congr 2

/-- If `Y` is positive definite, `R` and `Y - R` are positive semidefinite and
`det (Y - R) = det Y`, then `R = 0`. -/
lemma eq_zero_of_det_sub_eq (Y R : Matrix a a ℝ) (hY : Y.PosDef) (hR : R.PosSemidef)
    (hQ : (Y - R).PosSemidef) (hdet : (Y - R).det = Y.det) : R = 0 := by
  obtain ⟨U, hU1, hU2, hYU⟩ := real_spectral Y hY.isHermitian
  set ev := hY.isHermitian.eigenvalues
  have hev : ∀ i, 0 < ev i := fun i => hY.eigenvalues_pos i
  set B : Matrix a a ℝ := U * diagonal (fun i => Real.sqrt (ev i)) with hB
  have hBB : B * Bᵀ = Y := by
    rw [hYU, hB, Matrix.transpose_mul, Matrix.diagonal_transpose]
    have : diagonal (fun i => Real.sqrt (ev i)) * diagonal (fun i => Real.sqrt (ev i)) =
        diagonal ev := by
      rw [Matrix.diagonal_mul_diagonal]
      congr 1; funext i; exact Real.mul_self_sqrt (hev i).le
    calc U * diagonal (fun i => Real.sqrt (ev i)) * (diagonal (fun i => Real.sqrt (ev i)) * Uᵀ)
        = U * (diagonal (fun i => Real.sqrt (ev i)) * diagonal (fun i => Real.sqrt (ev i))) * Uᵀ := by
          simp only [Matrix.mul_assoc]
      _ = U * diagonal ev * Uᵀ := by rw [this]
  have hdetY : 0 < Y.det := hY.det_pos
  have hdetB : B.det ≠ 0 := by
    intro h0
    have : Y.det = B.det * B.det := by rw [← hBB, Matrix.det_mul, Matrix.det_transpose]
    rw [h0, zero_mul] at this
    linarith
  have hBu : IsUnit B := (Matrix.isUnit_iff_isUnit_det B).mpr (isUnit_iff_ne_zero.mpr hdetB)
  have hBtu : IsUnit Bᵀ := by
    rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_transpose]; exact isUnit_iff_ne_zero.mpr hdetB
  set Bi := B⁻¹ with hBi
  have hBiB : Bi * B = 1 := Matrix.nonsing_inv_mul B ((Matrix.isUnit_iff_isUnit_det B).mp hBu)
  have hBBi : B * Bi = 1 := Matrix.mul_nonsing_inv B ((Matrix.isUnit_iff_isUnit_det B).mp hBu)
  have hBtBit : Bᵀ * Biᵀ = 1 := by rw [← Matrix.transpose_mul, hBiB, Matrix.transpose_one]
  have hBitBt : Biᵀ * Bᵀ = 1 := by rw [← Matrix.transpose_mul, hBBi, Matrix.transpose_one]
  have hct : ∀ X : Matrix a a ℝ, Xᴴ = Xᵀ := fun X => Matrix.conjTranspose_eq_transpose_of_trivial X
  set M := Bi * R * Biᵀ with hM
  have hMpsd : M.PosSemidef := by
    have := hR.mul_mul_conjTranspose_same Bi
    rwa [hct] at this
  have hYc : Bi * Y * Biᵀ = 1 := by
    rw [← hBB]
    calc Bi * (B * Bᵀ) * Biᵀ = (Bi * B) * (Bᵀ * Biᵀ) := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hBiB, hBtBit, Matrix.one_mul]
  have hN : Bi * (Y - R) * Biᵀ = 1 - M := by
    rw [Matrix.mul_sub, Matrix.sub_mul, hYc]
  have hNpsd : (1 - M).PosSemidef := by
    rw [← hN]
    have := hQ.mul_mul_conjTranspose_same Bi
    rwa [hct] at this
  have hdetN : (1 - M).det = 1 := by
    have h1 : (Bi * Y * Biᵀ).det = 1 := by rw [hYc, Matrix.det_one]
    rw [← hN]
    rw [Matrix.det_mul, Matrix.det_mul] at h1 ⊢
    rw [hdet]; exact h1
  -- diagonalize M
  obtain ⟨V, hV1, hV2, hMV⟩ := real_spectral M hMpsd.isHermitian
  set lam := hMpsd.isHermitian.eigenvalues
  have hlam0 : ∀ i, 0 ≤ lam i := fun i => hMpsd.eigenvalues_nonneg i
  have h1M : 1 - M = V * diagonal (fun i => 1 - lam i) * Vᵀ := by
    have : diagonal (fun i => 1 - lam i) = 1 - diagonal lam := by
      ext i j; by_cases h : i = j <;> simp [h]
    rw [this, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hV1, ← hMV]
  have hD : (diagonal (fun i => 1 - lam i)).PosSemidef := by
    have := hNpsd.conjTranspose_mul_mul_same V
    rw [hct, h1M] at this
    convert this using 1
    calc diagonal (fun i => 1 - lam i) = (Vᵀ * V) * diagonal (fun i => 1 - lam i) * (Vᵀ * V) := by
          rw [hV2, Matrix.one_mul, Matrix.mul_one]
      _ = Vᵀ * (V * diagonal (fun i => 1 - lam i) * Vᵀ) * V := by simp only [Matrix.mul_assoc]
  have hle1 : ∀ i, 0 ≤ 1 - lam i := fun i => by
    have := hD.diag_nonneg (i := i)
    simpa [Matrix.diagonal_apply] using this
  have hprod : ∏ i, (1 - lam i) = 1 := by
    have : (1 - M).det = ∏ i, (1 - lam i) := by
      rw [h1M, Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal, Matrix.det_transpose]
      have hVV : V.det * V.det = 1 := by
        have := congrArg Matrix.det hV1
        rwa [Matrix.det_mul, Matrix.det_transpose, Matrix.det_one] at this
      calc V.det * (∏ i, (1 - lam i)) * V.det = (V.det * V.det) * ∏ i, (1 - lam i) := by ring
        _ = ∏ i, (1 - lam i) := by rw [hVV, one_mul]
    rw [← this, hdetN]
  have hlam : lam = 0 := by
    funext i
    have hrest : ∏ j ∈ Finset.univ.erase i, (1 - lam j) ≤ 1 :=
      Finset.prod_le_one (fun j _ => hle1 j) (fun j _ => by linarith [hlam0 j])
    have := Finset.mul_prod_erase Finset.univ (fun j => 1 - lam j) (Finset.mem_univ i)
    rw [hprod] at this
    have h2 : (1 - lam i) * ∏ j ∈ Finset.univ.erase i, (1 - lam j) ≤ 1 - lam i :=
      mul_le_of_le_one_right (hle1 i) hrest
    have := hlam0 i
    simp only [Pi.zero_apply]
    linarith
  have hM0 : M = 0 := hMpsd.isHermitian.eigenvalues_eq_zero_iff.mp hlam
  calc R = (B * Bi) * R * (Biᵀ * Bᵀ) := by rw [hBBi, hBitBt, Matrix.one_mul, Matrix.mul_one]
    _ = B * M * Bᵀ := by simp only [hM, Matrix.mul_assoc]
    _ = 0 := by rw [hM0, Matrix.mul_zero, Matrix.zero_mul]

end X5FullRank

namespace X5FullRank

lemma cp_quadratic {n : ℕ} (X Y : Matrix (Phase n) (Phase n) ℝ) (x y : Phase n → ℝ) :
    RCLike.re (star (fun j => (x j : ℂ) + (y j : ℂ) * Complex.I) ⬝ᵥ
      (cpMatrix X Y *ᵥ (fun j => (x j : ℂ) + (y j : ℂ) * Complex.I))) =
      x ⬝ᵥ (Y *ᵥ x) + y ⬝ᵥ (Y *ᵥ y) + x ⬝ᵥ (commutatorDefect X *ᵥ y)
        - y ⬝ᵥ (commutatorDefect X *ᵥ x) := by
  set S := commutatorDefect X
  simp only [dotProduct, Matrix.mulVec, Finset.mul_sum, ← Finset.sum_add_distrib,
    ← Finset.sum_sub_distrib, Pi.star_apply, RCLike.re_to_complex, Complex.re_sum]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
  simp only [cpMatrix, complexify, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, S]
  simp [Complex.mul_re, Complex.mul_im]
  ring

end X5FullRank

open X5FullRank in
theorem solution {n : ℕ} (hn : 0 < n)
    (X Y : Matrix (Phase n) (Phase n) ℝ) (hCP : (cpMatrix X Y).PosSemidef)
    (hY : Y.rank = 2 * n) (hSigma : (commutatorDefect X).rank = 2 * n) :
    (minimalNoise X Y ↔
      Y = commutatorDefect X * Y⁻¹ * (commutatorDefect X).transpose) ∧
    (minimalNoise X Y ↔ Y.det = (commutatorDefect X).det) ∧
    (minimalNoise X Y ↔
      ((commutatorDefect X).rank : ℤ) =
        (Y.rank : ℤ) - ((rankResidual Y (commutatorDefect X)).rank : ℤ)) := by
  have hcrit := x5_supportInverseCriterion hn X Y hCP
  set S := commutatorDefect X with hSdef
  have hcard : Fintype.card (Phase n) = 2 * n := by simp [Phase, Fintype.card_sum]; ring
  have hsig : (sigma n)ᵀ = -sigma n := by
    simp [sigma, Matrix.fromBlocks_transpose, Matrix.fromBlocks_neg]
  have hSt : Sᵀ = -S := by
    simp only [S, commutatorDefect, Matrix.transpose_sub, Matrix.transpose_mul,
      Matrix.transpose_transpose, hsig]
    simp only [Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_assoc]
    abel
  have hYt : Yᵀ = Y := by
    ext i j
    have h := hCP.isHermitian.apply j i
    have h2 := congrArg Complex.re h
    simp [cpMatrix, complexify, Matrix.sub_apply] at h2
    simpa [Matrix.transpose_apply] using h2.symm
  have hct : ∀ A : Matrix (Phase n) (Phase n) ℝ, Aᴴ = Aᵀ :=
    fun A => Matrix.conjTranspose_eq_transpose_of_trivial A
  have hquad : ∀ x y : Phase n → ℝ,
      0 ≤ x ⬝ᵥ (Y *ᵥ x) + y ⬝ᵥ (Y *ᵥ y) + x ⬝ᵥ (S *ᵥ y) - y ⬝ᵥ (S *ᵥ x) := by
    intro x y
    rw [← cp_quadratic]
    exact hCP.re_dotProduct_nonneg _
  have hdetY0 : Y.det ≠ 0 := det_ne_zero_of_rank Y (by rw [hY, hcard])
  have hdetS0 : S.det ≠ 0 := det_ne_zero_of_rank S (by rw [hSigma, hcard])
  have hYu : IsUnit Y := (Matrix.isUnit_iff_isUnit_det Y).mpr (isUnit_iff_ne_zero.mpr hdetY0)
  have hYpsd : Y.PosSemidef := by
    refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ fun x => ?_
    · rw [Matrix.IsHermitian, hct, hYt]
    · have := hquad x 0
      simpa using this
  have hYpd : Y.PosDef := hYpsd.posDef_iff_det_ne_zero.mpr hdetY0
  have hdetYpos : 0 < Y.det := hYpd.det_pos
  have hdetSpos : 0 < S.det := lt_of_le_of_ne (det_nonneg_of_skew S hSt) (Ne.symm hdetS0)
  have hsupp : supportInverse Y = Y⁻¹ := supportInverse_of_isUnit Y hYu
  have h1 : minimalNoise X Y ↔ Y = S * Y⁻¹ * Sᵀ := by rw [hcrit, hsupp]
  -- the Schur complement residual is positive semidefinite
  have hRpsd : (Y - S * Y⁻¹ * Sᵀ).PosSemidef := by
    haveI : Invertible Y := hYu.invertible
    have hblock : (Matrix.fromBlocks Y S Sᴴ Y).PosSemidef := by
      refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ fun v => ?_
      · rw [Matrix.IsHermitian, Matrix.fromBlocks_conjTranspose, Matrix.conjTranspose_conjTranspose,
          hct Y, hYt]
      · rw [← Sum.elim_comp_inl_inr v, Matrix.fromBlocks_mulVec]
        simp only [star_trivial, sumElim_dotProduct_sumElim, dotProduct_add, hct S, hSt,
          Matrix.neg_mulVec, dotProduct_neg, Sum.elim_comp_inl, Sum.elim_comp_inr]
        have := hquad (v ∘ Sum.inl) (v ∘ Sum.inr)
        linarith
    have := (Matrix.PosDef.fromBlocks₂₂ Y S hYpd).mp hblock
    rwa [hct] at this
  have hdetQ : (S * Y⁻¹ * Sᵀ).det = S.det * S.det / Y.det := by
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, Matrix.det_nonsing_inv,
      Ring.inverse_eq_inv']
    field_simp
  refine ⟨h1, ?_, ?_⟩
  · rw [h1]
    constructor
    · intro h
      have hd : Y.det = S.det * S.det / Y.det := by rw [← hdetQ, ← h]
      have : Y.det * Y.det = S.det * S.det := by
        field_simp at hd; linarith
      nlinarith
    · intro hd
      have hQpsd : (Y - (Y - S * Y⁻¹ * Sᵀ)).PosSemidef := by
        rw [sub_sub_cancel]
        have := hYpd.inv.posSemidef.mul_mul_conjTranspose_same S
        rwa [hct] at this
      have hdet' : (Y - (Y - S * Y⁻¹ * Sᵀ)).det = Y.det := by
        rw [sub_sub_cancel, hdetQ, ← hd]
        field_simp
      have := eq_zero_of_det_sub_eq Y _ hYpd hRpsd hQpsd hdet'
      exact (sub_eq_zero.mp this)
  · rw [h1]
    have hres : rankResidual Y S = Y - S * Y⁻¹ * Sᵀ := by
      simp [rankResidual, hsupp]
    rw [hres, hY, hSigma]
    constructor
    · intro h
      rw [← h, sub_self, Matrix.rank_zero]; simp
    · intro h
      have h0 : (Y - S * Y⁻¹ * Sᵀ).rank = 0 := by omega
      exact sub_eq_zero.mp (eq_zero_of_rank_zero _ h0)
