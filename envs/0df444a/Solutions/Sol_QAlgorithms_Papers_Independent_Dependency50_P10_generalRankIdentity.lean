-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Dependency50.P10.generalRankIdentity
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T06:35:30.390825+00:00
-- url     : https://prove2.me/submissions/62ba7ffb-6cea-44e9-8afc-781f372a185c

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P10

noncomputable section

open scoped ComplexOrder
open Matrix QAlgorithms.Papers.Independent.Dependency50.P10

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

end X5KernelRank

open X5KernelRank in
theorem solution {m : ℕ} (A B : Matrix (Fin m) (Fin m) ℝ)
    (hB : B.transpose = -B)
    (hCP : (complexify A - Complex.I • complexify B).PosSemidef) :
    (2 * (complexify A - Complex.I • complexify B).rank =
      (complexify A).rank + (complexify (rankResidual A B)).rank) ∧
    (((complexify A).rank : ℤ) - ((complexify (rankResidual A B)).rank : ℤ) ≤
      ((complexify B).rank : ℤ)) := by
  set Y := A with hYdef
  set S := B with hSdef
  set K := complexify A - Complex.I • complexify B with hKdef
  set Yc := complexify Y
  set Sc := complexify S
  have hSt : Sᵀ = -S := hB
  -- symmetry of `Y` from hermiticity of `K`
  have hYt : Yᵀ = Y := by
    ext i j
    have h := hCP.isHermitian.apply j i
    have h2 := congrArg Complex.re h
    simp [K, complexify, Matrix.sub_apply] at h2
    simpa [Matrix.transpose_apply] using h2.symm
  have hKmv : ∀ v, K *ᵥ v = Yc *ᵥ v - Complex.I • (Sc *ᵥ v) := fun v => by
    simp [K, Matrix.sub_mulVec, Matrix.smul_mulVec, Yc, Sc, S, Y]
  have hKt : Kᵀ = Yc + Complex.I • Sc := by
    have : Scᵀ = -Sc := by simp only [Sc, ← cx_transpose, hSt, cx_neg]
    simp [K, Matrix.transpose_sub, Matrix.transpose_smul, ← cx_transpose, hYt, Yc,
      this, Sc, S, Y, sub_eq_add_neg]
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
  have mv : ∀ (M N : Matrix (Fin m) (Fin m) ℂ) (v : Fin m → ℂ), M *ᵥ (N *ᵥ v) = (M * N) *ᵥ v :=
    fun M N v => Matrix.mulVec_mulVec _ _ _
  set J : Matrix (Fin m) (Fin m) ℂ := Complex.I • (Ypc * Sc) with hJdef
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
  -- dimension count
  have dA := Submodule.finrank_sup_add_finrank_inf_eq kY Ep
  have dB := Submodule.finrank_sup_add_finrank_inf_eq kY Em
  have dC := Submodule.finrank_sup_add_finrank_inf_eq kY (Ep ⊔ Em)
  have dE := Submodule.finrank_sup_add_finrank_inf_eq Ep Em
  rw [← hA_sup, hA_inf, finrank_bot] at dA
  rw [← hB_sup, hB_inf, finrank_bot] at dB
  rw [← hC_sup, hC_inf, finrank_bot] at dC
  rw [hEE, finrank_bot] at dE
  have rK := rank_add_finrank_ker K
  have rKt := rank_add_finrank_ker Kᵀ
  have rY : Yc.rank + Module.finrank ℂ kY = Fintype.card (Fin m) := rank_add_finrank_ker Yc
  have rR := rank_add_finrank_ker Rc
  have rS := rank_add_finrank_ker Sc
  have hKtr : Kᵀ.rank = K.rank := Matrix.rank_transpose K
  have hmono1 := Submodule.finrank_mono part3
  have hkR : kY ≤ complexKernel Rc := by rw [hC_sup]; exact le_sup_left
  have hmono2 := Submodule.finrank_mono hkR
  have hRS : complexKernel Rc ⊓ complexKernel Sc ≤ kY := fun v hv => by
    rw [Submodule.mem_inf, mem_cker, mem_cker] at hv
    rw [mem_cker]
    have := hv.1
    rw [hRmv, hv.2] at this
    simpa using this
  have dRS := Submodule.finrank_sup_add_finrank_inf_eq (complexKernel Rc) (complexKernel Sc)
  have hle1 := Submodule.finrank_mono hRS
  have hle2 := Submodule.finrank_le (complexKernel Rc ⊔ complexKernel Sc)
  rw [Module.finrank_fintype_fun_eq_card] at hle2
  refine ⟨?_, ?_⟩
  · omega
  · push_cast; omega
