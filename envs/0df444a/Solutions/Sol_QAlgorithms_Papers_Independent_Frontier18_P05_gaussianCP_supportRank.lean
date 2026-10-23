-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Frontier18.P05.gaussianCP_supportRank
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T06:46:45.345432+00:00
-- url     : https://prove2.me/submissions/72409ee6-232c-4cba-880e-3fd5b6a7c22e

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

end X5KernelRank

open X5KernelRank in
theorem solution {n : ℕ} (hn : 0 < n)
    (X Y : Matrix (Phase n) (Phase n) ℝ) (hCP : (cpMatrix X Y).PosSemidef) :
    (commutatorDefect X).transpose = -commutatorDefect X ∧
    LinearMap.range (commutatorDefect X).mulVecLin ≤ LinearMap.range Y.mulVecLin ∧
    (commutatorDefect X).rank ≤ Y.rank ∧ Y.rank ≤ 2 * n ∧
    Even (commutatorDefect X).rank ∧
    ((Y.rank = 2 * n ∧ (commutatorDefect X).rank = 2 * n) ∨
     (Y.rank = 2 * n ∧ (commutatorDefect X).rank < 2 * n) ∨
     (Y.rank < 2 * n ∧ (commutatorDefect X).rank ≤ Y.rank)) := by
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
  -- range inclusion
  have hPS := M_PS Y hYt S hSt hkerR
  have hYYp := M_AAp Y hYt
  have hrange : LinearMap.range S.mulVecLin ≤ LinearMap.range Y.mulVecLin := by
    rintro _ ⟨v, rfl⟩
    refine ⟨supportInverse Y *ᵥ (S *ᵥ v), ?_⟩
    simp only [Matrix.mulVecLin_apply]
    rw [Matrix.mulVec_mulVec, hYYp, Matrix.mulVec_mulVec, hPS]
  have hrank : S.rank ≤ Y.rank := Submodule.finrank_mono hrange
  have hY2n : Y.rank ≤ 2 * n := by
    have := Matrix.rank_le_card_width Y
    simp only [Phase, Fintype.card_sum, Fintype.card_fin] at this
    omega
  have heven : Even S.rank := by
    rw [Matrix.rank_eq_finrank_range_toLin S (PiLp.basisFun 2 ℝ (Phase n))
      (PiLp.basisFun 2 ℝ (Phase n))]
    refine even_finrank_range_of_skew _ ?_
    have h1 := Matrix.toEuclideanLin_conjTranspose_eq_adjoint S
    rw [Matrix.conjTranspose_eq_transpose_of_trivial, hSt, map_neg] at h1
    exact h1.symm
  refine ⟨hSt, hrange, hrank, hY2n, heven, ?_⟩
  omega
