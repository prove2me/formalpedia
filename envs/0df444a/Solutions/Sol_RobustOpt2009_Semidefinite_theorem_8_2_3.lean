-- Prove2me | solution 1 for RobustOpt2009.Semidefinite.theorem_8_2_3
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-23T03:34:10.106195+00:00
-- url     : https://prove2.me/submissions/a053277c-6626-4d91-82d9-e504ed3b0b46

import Mathlib
import Theorems.Thm_ModernConvex_SLemma_s_lemma

open Matrix
open scoped Matrix.Norms.L2Operator

namespace X8LMI

noncomputable def nrm {k : Type*} [Fintype k] (v : k → ℝ) : ℝ := Real.sqrt (∑ i, v i ^ 2)

variable {k m n : Type*} [Fintype k] [Fintype m] [Fintype n] [DecidableEq n]

lemma nrm_nonneg (v : k → ℝ) : 0 ≤ nrm v := Real.sqrt_nonneg _

lemma nrm_sq (v : k → ℝ) : nrm v ^ 2 = v ⬝ᵥ v := by
  rw [nrm, Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _)]
  simp [dotProduct, sq]

lemma euc_norm (v : k → ℝ) : ‖(WithLp.toLp 2 v : EuclideanSpace ℝ k)‖ = nrm v := by
  rw [EuclideanSpace.norm_eq]
  simp [nrm, Real.norm_eq_abs, sq_abs]

lemma cs (u v : k → ℝ) : |u ⬝ᵥ v| ≤ nrm u * nrm v := by
  have h := abs_real_inner_le_norm (WithLp.toLp 2 u : EuclideanSpace ℝ k) (WithLp.toLp 2 v)
  rw [euc_norm, euc_norm] at h
  convert h using 2
  simp [dotProduct, PiLp.inner_apply, mul_comm]

lemma op_bound (ζ : Matrix m n ℝ) (v : n → ℝ) : nrm (ζ *ᵥ v) ≤ ‖ζ‖ * nrm v := by
  have h := l2_opNorm_mulVec ζ (WithLp.toLp 2 v)
  simp only [euc_norm] at h
  rw [← euc_norm (ζ *ᵥ v)]
  simpa using h

lemma bil (ζ : Matrix m n ℝ) (u : m → ℝ) (v : n → ℝ) :
    |u ⬝ᵥ (ζ *ᵥ v)| ≤ ‖ζ‖ * nrm u * nrm v := by
  refine (cs _ _).trans ?_
  have := mul_le_mul_of_nonneg_left (op_bound ζ v) (nrm_nonneg u)
  nlinarith [this]

lemma rank1 (a : m → ℝ) (b : n → ℝ) : ‖vecMulVec a b‖ ≤ nrm a * nrm b := by
  rw [l2_opNorm_def]
  refine ContinuousLinearMap.opNorm_le_bound _
    (mul_nonneg (nrm_nonneg _) (nrm_nonneg _)) fun w => ?_
  have e : ((toEuclideanLin.trans LinearMap.toContinuousLinearMap) (vecMulVec a b)) w =
      WithLp.toLp 2 ((b ⬝ᵥ WithLp.ofLp w) • a) := by
    ext i
    simp [vecMulVec_mulVec, mul_comm]
  rw [e, euc_norm]
  have hw : ‖w‖ = nrm (WithLp.ofLp w) := by rw [← euc_norm]
  rw [hw]
  have h1 : nrm ((b ⬝ᵥ WithLp.ofLp w) • a) = |b ⬝ᵥ WithLp.ofLp w| * nrm a := by
    rw [nrm, nrm, ← Real.sqrt_sq_eq_abs, ← Real.sqrt_mul (sq_nonneg _)]
    congr 1
    simp [mul_pow, Finset.mul_sum]
  rw [h1]
  have := cs b (WithLp.ofLp w)
  nlinarith [nrm_nonneg a, nrm_nonneg b, nrm_nonneg (WithLp.ofLp w), abs_nonneg (b ⬝ᵥ WithLp.ofLp w)]

end X8LMI

open Matrix
open scoped Matrix.Norms.L2Operator

namespace X8LMI

variable {p n q : ℕ}

lemma form_robust (A : Matrix (Fin n) (Fin n) ℝ) (L : Matrix (Fin p) (Fin n) ℝ)
    (R : Matrix (Fin q) (Fin n) ℝ) (ζ : Matrix (Fin p) (Fin q) ℝ) (x : Fin n → ℝ) :
    x ⬝ᵥ ((A + Lᵀ * ζ * R + Rᵀ * ζᵀ * L) *ᵥ x) =
      x ⬝ᵥ (A *ᵥ x) + 2 * ((L *ᵥ x) ⬝ᵥ (ζ *ᵥ (R *ᵥ x))) := by
  simp only [add_mulVec, dotProduct_add, ← mulVec_mulVec]
  rw [dotProduct_mulVec x Lᵀ, vecMul_transpose, dotProduct_mulVec x Rᵀ, vecMul_transpose,
    dotProduct_mulVec (R *ᵥ x) ζᵀ, vecMul_transpose, dotProduct_comm (ζ *ᵥ (R *ᵥ x))]
  ring

lemma real_psd_iff {ι : Type*} [Fintype ι] (M : Matrix ι ι ℝ) :
    M.PosSemidef ↔ Mᵀ = M ∧ ∀ x, 0 ≤ x ⬝ᵥ (M *ᵥ x) := by
  rw [posSemidef_iff_dotProduct_mulVec]
  simp [IsHermitian, conjTranspose_eq_transpose_of_trivial]

lemma robust_iff (A : Matrix (Fin n) (Fin n) ℝ) (L : Matrix (Fin p) (Fin n) ℝ)
    (R : Matrix (Fin q) (Fin n) ℝ) (hA : A.IsSymm) (ρ : ℝ) (hρ : 0 < ρ) :
    (∀ ζ : Matrix (Fin p) (Fin q) ℝ, ‖ζ‖ ≤ ρ → (A + Lᵀ * ζ * R + Rᵀ * ζᵀ * L).PosSemidef) ↔
      ∀ x, 2 * ρ * nrm (L *ᵥ x) * nrm (R *ᵥ x) ≤ x ⬝ᵥ (A *ᵥ x) := by
  constructor
  · intro h x
    have h0 := ((real_psd_iff _).mp (h 0 (by simp [hρ.le]))).2 x
    rw [form_robust] at h0
    simp only [zero_mulVec, dotProduct_zero, mul_zero, add_zero] at h0
    set a := nrm (L *ᵥ x)
    set b := nrm (R *ᵥ x)
    by_cases hab : a = 0 ∨ b = 0
    · rcases hab with h1 | h1 <;> simp [h1, h0]
    push Not at hab
    have ha : 0 < a := lt_of_le_of_ne (nrm_nonneg _) (Ne.symm hab.1)
    have hb : 0 < b := lt_of_le_of_ne (nrm_nonneg _) (Ne.symm hab.2)
    set ζ : Matrix (Fin p) (Fin q) ℝ := (-(ρ / (a * b))) • vecMulVec (L *ᵥ x) (R *ᵥ x)
    have hζ : ‖ζ‖ ≤ ρ := by
      rw [norm_smul, Real.norm_eq_abs, abs_neg, abs_of_pos (by positivity)]
      calc ρ / (a * b) * ‖vecMulVec (L *ᵥ x) (R *ᵥ x)‖ ≤ ρ / (a * b) * (a * b) :=
            mul_le_mul_of_nonneg_left (rank1 _ _) (by positivity)
        _ = ρ := by field_simp
    have h1 := ((real_psd_iff _).mp (h ζ hζ)).2 x
    rw [form_robust] at h1
    have e : (L *ᵥ x) ⬝ᵥ (ζ *ᵥ (R *ᵥ x)) = -(ρ * a * b) := by
      simp only [ζ, smul_mulVec, vecMulVec_mulVec, dotProduct_smul]
      have ea := nrm_sq (L *ᵥ x)
      have eb := nrm_sq (R *ᵥ x)
      simp only [MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op, smul_eq_mul] at *
      rw [← ea, ← eb]
      change -(ρ / (a * b)) * (a ^ 2 * b ^ 2) = _
      field_simp
    rw [e] at h1
    linarith
  · intro h ζ hζ
    rw [real_psd_iff]
    refine ⟨?_, fun x => ?_⟩
    · have hA' : Aᵀ = A := hA
      simp only [transpose_add, transpose_mul, transpose_transpose, hA', Matrix.mul_assoc]
      abel
    · rw [form_robust]
      have h1 := bil ζ (L *ᵥ x) (R *ᵥ x)
      have h2 := h x
      have h3 : ‖ζ‖ * nrm (L *ᵥ x) * nrm (R *ᵥ x) ≤ ρ * nrm (L *ᵥ x) * nrm (R *ᵥ x) := by
        have := mul_nonneg (nrm_nonneg (L *ᵥ x)) (nrm_nonneg (R *ᵥ x))
        nlinarith
      have := neg_abs_le ((L *ᵥ x) ⬝ᵥ (ζ *ᵥ (R *ᵥ x)))
      linarith

end X8LMI

open Matrix
open scoped Matrix.Norms.L2Operator

namespace X8LMI

variable {p n q : ℕ}

lemma qf_blocks (P : Matrix (Fin p) (Fin p) ℝ) (Q : Matrix (Fin p) (Fin n) ℝ)
    (D : Matrix (Fin n) (Fin n) ℝ) (ξ : Fin p → ℝ) (x : Fin n → ℝ) :
    Sum.elim ξ x ⬝ᵥ (fromBlocks P Q Qᵀ D *ᵥ Sum.elim ξ x) =
      ξ ⬝ᵥ (P *ᵥ ξ) + 2 * (ξ ⬝ᵥ (Q *ᵥ x)) + x ⬝ᵥ (D *ᵥ x) := by
  rw [fromBlocks_mulVec, Sum.elim_comp_inl, Sum.elim_comp_inr, sumElim_dotProduct_sumElim,
    dotProduct_add, dotProduct_add, dotProduct_mulVec x Qᵀ, vecMul_transpose,
    dotProduct_comm (Q *ᵥ x)]
  ring

lemma form_sub {ι κ : Type*} [Fintype ι] [Fintype κ] (M : Matrix κ κ ℝ) (e : ι ≃ κ)
    (x : ι → ℝ) :
    x ⬝ᵥ (M.submatrix e e *ᵥ x) = (x ∘ e.symm) ⬝ᵥ (M *ᵥ (x ∘ e.symm)) := by
  simp only [dotProduct, mulVec, submatrix_apply, Function.comp_apply]
  rw [← e.sum_comp]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Equiv.symm_apply_apply]
  congr 1
  rw [← e.sum_comp]
  simp only [Equiv.symm_apply_apply]

lemma qf_RR (R : Matrix (Fin q) (Fin n) ℝ) (x : Fin n → ℝ) :
    x ⬝ᵥ ((Rᵀ * R) *ᵥ x) = (R *ᵥ x) ⬝ᵥ (R *ᵥ x) := by
  rw [← mulVec_mulVec, dotProduct_mulVec, vecMul_transpose]

noncomputable def Bk (A : Matrix (Fin n) (Fin n) ℝ) (L : Matrix (Fin p) (Fin n) ℝ)
    (R : Matrix (Fin q) (Fin n) ℝ) (ρ lam : ℝ) : Matrix (Fin p ⊕ Fin n) (Fin p ⊕ Fin n) ℝ :=
  fromBlocks (lam • (1 : Matrix (Fin p) (Fin p) ℝ)) (ρ • L) (ρ • Lᵀ) (A - lam • (Rᵀ * R))

lemma Bk_form (A : Matrix (Fin n) (Fin n) ℝ) (L : Matrix (Fin p) (Fin n) ℝ)
    (R : Matrix (Fin q) (Fin n) ℝ) (ρ lam : ℝ) (ξ : Fin p → ℝ) (x : Fin n → ℝ) :
    Sum.elim ξ x ⬝ᵥ (Bk A L R ρ lam *ᵥ Sum.elim ξ x) =
      lam * (ξ ⬝ᵥ ξ) + 2 * ρ * (ξ ⬝ᵥ (L *ᵥ x)) + x ⬝ᵥ (A *ᵥ x) -
        lam * ((R *ᵥ x) ⬝ᵥ (R *ᵥ x)) := by
  have h := qf_blocks (lam • (1 : Matrix (Fin p) (Fin p) ℝ)) (ρ • L) (A - lam • (Rᵀ * R)) ξ x
  rw [transpose_smul] at h
  rw [Bk, h]
  simp only [sub_mulVec, dotProduct_sub, smul_mulVec, dotProduct_smul, one_mulVec, smul_eq_mul]
  rw [qf_RR]
  ring

theorem cert_iff (hp : 0 < p) (A : Matrix (Fin n) (Fin n) ℝ) (L : Matrix (Fin p) (Fin n) ℝ)
    (R : Matrix (Fin q) (Fin n) ℝ) (hA : A.IsSymm) (hR : R ≠ 0) (ρ : ℝ) (hρ : 0 < ρ) :
    (∀ x, 2 * ρ * nrm (L *ᵥ x) * nrm (R *ᵥ x) ≤ x ⬝ᵥ (A *ᵥ x)) ↔
      ∃ lam : ℝ, (Bk A L R ρ lam).PosSemidef := by
  constructor
  · intro h
    set e : Fin (p + n) ≃ (Fin p ⊕ Fin n) := finSumFinEquiv.symm
    obtain ⟨AS, hAS⟩ : ∃ M, M = fromBlocks (-1 : Matrix (Fin p) (Fin p) ℝ) 0 0ᵀ (Rᵀ * R) :=
      ⟨_, rfl⟩
    obtain ⟨BS, hBS⟩ : ∃ M, M = fromBlocks (0 : Matrix (Fin p) (Fin p) ℝ) (ρ • L) (ρ • L)ᵀ A :=
      ⟨_, rfl⟩
    have fA : ∀ ξ x, Sum.elim ξ x ⬝ᵥ (AS *ᵥ Sum.elim ξ x) = (R *ᵥ x) ⬝ᵥ (R *ᵥ x) - ξ ⬝ᵥ ξ := by
      intro ξ x
      rw [hAS, qf_blocks, qf_RR]
      simp [neg_mulVec]
      ring
    have fB : ∀ ξ x, Sum.elim ξ x ⬝ᵥ (BS *ᵥ Sum.elim ξ x) =
        2 * ρ * (ξ ⬝ᵥ (L *ᵥ x)) + x ⬝ᵥ (A *ᵥ x) := by
      intro ξ x
      rw [hBS, qf_blocks, smul_mulVec, dotProduct_smul]
      simp only [zero_mulVec, dotProduct_zero, smul_eq_mul]
      ring
    have hAh : (AS.submatrix e e).IsHermitian := by
      refine IsHermitian.submatrix ?_ _
      rw [hAS]
      refine IsHermitian.fromBlocks ?_ ?_ ?_
      · simp
      · simp [IsHermitian]
      · simp [IsHermitian, conjTranspose_eq_transpose_of_trivial, transpose_mul]
    have hBh : (BS.submatrix e e).IsHermitian := by
      refine IsHermitian.submatrix ?_ _
      rw [hBS]
      refine IsHermitian.fromBlocks ?_ ?_ ?_
      · simp [conjTranspose_eq_transpose_of_trivial]
      · simp [IsHermitian]
      · have hA' : Aᵀ = A := hA
        simp [IsHermitian, conjTranspose_eq_transpose_of_trivial, hA']
    have hfeas : ∃ x : Fin (p + n) → ℝ, 0 < x ⬝ᵥ (AS.submatrix e e *ᵥ x) := by
      obtain ⟨i, j, hij⟩ : ∃ i j, R i j ≠ 0 := by
        by_contra hc
        push Not at hc
        exact hR (Matrix.ext hc)
      refine ⟨Sum.elim 0 (Pi.single j 1) ∘ e, ?_⟩
      rw [form_sub]
      simp only [Function.comp_assoc, Equiv.self_comp_symm, Function.comp_id]
      rw [fA]
      simp only [dotProduct_zero, sub_zero]
      have hRj : (R *ᵥ Pi.single j 1) i = R i j := by simp [mulVec_single]
      calc (0 : ℝ) < (R *ᵥ Pi.single j 1) i * (R *ᵥ Pi.single j 1) i := by
            rw [hRj]; exact mul_self_pos.mpr hij
        _ ≤ _ := by
          simp only [dotProduct]
          exact Finset.single_le_sum (f := fun k => (R *ᵥ Pi.single j 1) k *
            (R *ᵥ Pi.single j 1) k) (fun k _ => mul_self_nonneg _) (Finset.mem_univ i)
    obtain ⟨lam, hlam, hP⟩ := (ModernConvex.SLemma.s_lemma _ _ hAh hBh hfeas).mp (by
      intro z hz
      rw [form_sub] at hz ⊢
      set w := z ∘ e.symm
      have hw : w = Sum.elim (w ∘ Sum.inl) (w ∘ Sum.inr) := (Sum.elim_comp_inl_inr w).symm
      rw [hw] at hz ⊢
      rw [fA] at hz
      rw [fB]
      set ξ := w ∘ Sum.inl
      set x := w ∘ Sum.inr
      have h1 := nrm_sq ξ
      have h2 := nrm_sq (R *ᵥ x)
      have hle : nrm ξ ≤ nrm (R *ᵥ x) := by
        nlinarith [nrm_nonneg ξ, nrm_nonneg (R *ᵥ x)]
      have hc := cs ξ (L *ᵥ x)
      have hx := h x
      have := mul_le_mul_of_nonneg_right hle (nrm_nonneg (L *ᵥ x))
      have := neg_abs_le (ξ ⬝ᵥ (L *ᵥ x))
      nlinarith)
    refine ⟨lam, ?_⟩
    have hsub : BS.submatrix e e - lam • AS.submatrix e e = (BS - lam • AS).submatrix e e := by
      ext i j; simp
    rw [hsub, posSemidef_submatrix_equiv] at hP
    convert hP using 1
    rw [hAS, hBS, Bk]
    ext i j
    rcases i with i | i <;> rcases j with j | j <;> simp [sub_eq_add_neg]
  · rintro ⟨lam, hP⟩ x
    have hP' := (real_psd_iff _).mp hP
    have hlam : 0 ≤ lam := by
      have := hP'.2 (Sum.elim (Pi.single ⟨0, hp⟩ 1) 0)
      rw [Bk_form] at this
      simpa using this
    have hRR : 0 ≤ (R *ᵥ x) ⬝ᵥ (R *ᵥ x) := by
      rw [← nrm_sq]; positivity
    set a := nrm (L *ᵥ x)
    set b := nrm (R *ᵥ x)
    by_cases ha : a = 0
    · have := hP'.2 (Sum.elim 0 x)
      rw [Bk_form] at this
      simp only [dotProduct_zero, zero_dotProduct, mul_zero, zero_add] at this
      rw [ha]
      nlinarith [mul_nonneg hlam hRR]
    have ha' : 0 < a := lt_of_le_of_ne (nrm_nonneg _) (Ne.symm ha)
    have := hP'.2 (Sum.elim (-(b / a) • (L *ᵥ x)) x)
    rw [Bk_form] at this
    have ea := nrm_sq (L *ᵥ x)
    have eb := nrm_sq (R *ᵥ x)
    simp only [smul_dotProduct, dotProduct_smul, smul_eq_mul] at this
    rw [← ea, ← eb] at this
    change 0 ≤ lam * (-(b / a) * (-(b / a) * a ^ 2)) + 2 * ρ * (-(b / a) * a ^ 2) +
      x ⬝ᵥ (A *ᵥ x) - lam * b ^ 2 at this
    have e1 : -(b / a) * (-(b / a) * a ^ 2) = b ^ 2 := by field_simp
    have e2 : -(b / a) * a ^ 2 = -(a * b) := by field_simp
    rw [e1, e2] at this
    nlinarith

end X8LMI

open Matrix
open scoped Matrix.Norms.L2Operator

theorem solution {d n p q : ℕ} (hp : 0 < p)
    (A : (Fin d → ℝ) →ᵃ[ℝ] Matrix (Fin n) (Fin n) ℝ)
    (L : (Fin d → ℝ) →ᵃ[ℝ] Matrix (Fin p) (Fin n) ℝ)
    (hA : ∀ y, (A y).IsSymm)
    (R : Matrix (Fin q) (Fin n) ℝ) (hR : R ≠ 0)
    (ρ : ℝ) (hρ : 0 < ρ) (y : Fin d → ℝ) :
    (∀ ζ : Matrix (Fin p) (Fin q) ℝ, ‖ζ‖ ≤ ρ →
      (A y + (L y)ᵀ * ζ * R + Rᵀ * ζᵀ * L y).PosSemidef) ↔
    ∃ lam : ℝ,
      (fromBlocks (lam • (1 : Matrix (Fin p) (Fin p) ℝ))
        (ρ • L y) (ρ • (L y)ᵀ) (A y - lam • (Rᵀ * R))).PosSemidef :=
  (X8LMI.robust_iff (A y) (L y) R (hA y) ρ hρ).trans
    (X8LMI.cert_iff hp (A y) (L y) R (hA y) hR ρ hρ)
