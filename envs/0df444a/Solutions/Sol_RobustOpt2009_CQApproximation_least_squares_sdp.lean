-- Prove2me | solution 1 for RobustOpt2009.CQApproximation.least_squares_sdp
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-31T05:38:01.21177+00:00
-- url     : https://prove2.me/submissions/1a40b803-518d-4c48-9c4d-d5db90ce5a97
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_RobustOpt2009_CQApproximation_LeastSquares
import Theorems.Thm_RobustOpt2009_CQApproximation_matrix_cube
import Theorems.Thm_RobustOpt2009_CQApproximation_arrow_psd
import Theorems.Thm_ModernConvex_SLemma_s_lemma

open Matrix
open scoped BigOperators

namespace LSSDPAux

open RobustOpt2009.CQApproximation

/-- Euclidean norm of a coordinate vector. -/
noncomputable abbrev nv {n : Type*} [Fintype n] (v : n → ℝ) : ℝ :=
  ‖(WithLp.toLp 2 v : EuclideanSpace ℝ n)‖

lemma nv_sq {n : Type*} [Fintype n] (v : n → ℝ) : nv v ^ 2 = v ⬝ᵥ v := by
  rw [nv, ← real_inner_self_eq_norm_sq, EuclideanSpace.inner_toLp_toLp]
  simp

lemma nv_nonneg {n : Type*} [Fintype n] (v : n → ℝ) : 0 ≤ nv v := norm_nonneg _

lemma abs_dot_le {n : Type*} [Fintype n] (v w : n → ℝ) : |v ⬝ᵥ w| ≤ nv v * nv w := by
  have h := abs_real_inner_le_norm (WithLp.toLp 2 w : EuclideanSpace ℝ n)
    (WithLp.toLp 2 v : EuclideanSpace ℝ n)
  rw [EuclideanSpace.inner_toLp_toLp] at h
  simpa [mul_comm] using h

lemma dot_le {n : Type*} [Fintype n] (v w : n → ℝ) : v ⬝ᵥ w ≤ nv v * nv w :=
  (le_abs_self _).trans (abs_dot_le v w)

lemma nv_smul {n : Type*} [Fintype n] (c : ℝ) (v : n → ℝ) : nv (c • v) = |c| * nv v := by
  rw [nv, nv, WithLp.toLp_smul, norm_smul, Real.norm_eq_abs]

lemma nv_le_of_dot {n m : Type*} [Fintype n] [Fintype m] (v : n → ℝ) (w : m → ℝ)
    (h : v ⬝ᵥ v ≤ w ⬝ᵥ w) : nv v ≤ nv w := by
  have h1 := nv_sq v; have h2 := nv_sq w
  have := nv_nonneg v; have := nv_nonneg w
  nlinarith

lemma opBound_transpose {p q : ℕ} (η : Matrix (Fin p) (Fin q) ℝ) (hη : OperatorBound η 1)
    (w : Fin p → ℝ) : nv (ηᵀ *ᵥ w) ≤ nv w := by
  set z := ηᵀ *ᵥ w
  have h1 : z ⬝ᵥ z = w ⬝ᵥ (η *ᵥ z) := by
    simp only [z]
    rw [Matrix.mulVec_transpose, Matrix.dotProduct_mulVec]
  have h2 := dot_le w (η *ᵥ z)
  have h3 : nv (η *ᵥ z) ≤ nv z := by simpa using hη z
  have h4 := nv_sq z
  have := nv_nonneg z; have := nv_nonneg w; have := nv_nonneg (η *ᵥ z)
  nlinarith [mul_le_mul_of_nonneg_left h3 (nv_nonneg w)]

lemma sum_elim_dot {a b : Type*} [Fintype a] [Fintype b] (u v : a → ℝ) (x y : b → ℝ) :
    Sum.elim u x ⬝ᵥ Sum.elim v y = u ⬝ᵥ v + x ⬝ᵥ y := by
  simp [dotProduct, Fintype.sum_sum_type]

/-- Quadratic form of the symmetric block term. -/
lemma quad_blockTerm {ι : Type*} [Fintype ι] {p q : ℕ} (L : Matrix (Fin p) ι ℝ)
    (R : Matrix (Fin q) ι ℝ) (η : Matrix (Fin p) (Fin q) ℝ) (x : ι → ℝ) :
    x ⬝ᵥ ((Lᵀ * η * R + Rᵀ * ηᵀ * L) *ᵥ x) = 2 * ((L *ᵥ x) ⬝ᵥ (η *ᵥ (R *ᵥ x))) := by
  rw [Matrix.add_mulVec, dotProduct_add, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,
    Matrix.dotProduct_mulVec x Rᵀ, ← Matrix.mulVec_transpose, ← Matrix.mulVec_transpose,
    Matrix.transpose_transpose, Matrix.transpose_transpose, dotProduct_comm (R *ᵥ x)]
  rw [Matrix.mulVec_transpose, ← Matrix.dotProduct_mulVec]
  ring

lemma herm_blockTerm {ι : Type*} [Fintype ι] {p q : ℕ} (L : Matrix (Fin p) ι ℝ)
    (R : Matrix (Fin q) ι ℝ) (η : Matrix (Fin p) (Fin q) ℝ) :
    (Lᵀ * η * R + Rᵀ * ηᵀ * L).IsHermitian := by
  unfold Matrix.IsHermitian
  rw [Matrix.conjTranspose_eq_transpose_of_trivial]
  simp [Matrix.transpose_add, Matrix.transpose_mul, Matrix.mul_assoc, add_comm]

/-- The homogeneous S-lemma, transported to an arbitrary finite index type. -/
lemma s_lemma_gen {κ : Type*} [Fintype κ] [DecidableEq κ] (A B : Matrix κ κ ℝ)
    (hA : A.IsHermitian) (hB : B.IsHermitian) (hfeas : ∃ z : κ → ℝ, 0 < z ⬝ᵥ (A *ᵥ z))
    (himp : ∀ z : κ → ℝ, 0 ≤ z ⬝ᵥ (A *ᵥ z) → 0 ≤ z ⬝ᵥ (B *ᵥ z)) :
    ∃ lam : ℝ, 0 ≤ lam ∧ (B - lam • A).PosSemidef := by
  set e := Fintype.equivFin κ
  have hq : ∀ (M : Matrix κ κ ℝ) (x : Fin (Fintype.card κ) → ℝ),
      x ⬝ᵥ (M.submatrix e.symm e.symm *ᵥ x) = (x ∘ e) ⬝ᵥ (M *ᵥ (x ∘ e)) := by
    intro M x
    rw [Matrix.submatrix_mulVec_equiv]
    simp only [Equiv.symm_symm]
    rw [dotProduct_comp_equiv_symm]
  have key := (ModernConvex.SLemma.s_lemma (A.submatrix e.symm e.symm)
    (B.submatrix e.symm e.symm) (hA.submatrix _) (hB.submatrix _) (by
      obtain ⟨z, hz⟩ := hfeas
      refine ⟨z ∘ e.symm, ?_⟩
      rw [hq]; simpa [Function.comp_def] using hz)).1 (by
      intro x hx
      rw [hq] at hx ⊢
      exact himp _ hx)
  obtain ⟨lam, hlam, hpsd⟩ := key
  refine ⟨lam, hlam, ?_⟩
  have : (B - lam • A).submatrix e.symm e.symm =
      B.submatrix e.symm e.symm - lam • A.submatrix e.symm e.symm := by
    ext i j; simp
  rw [← this] at hpsd
  exact (Matrix.posSemidef_submatrix_equiv e.symm).1 hpsd

lemma exists_mulVec_ne {ι : Type*} [Fintype ι] [DecidableEq ι] {p : ℕ}
    (L : Matrix (Fin p) ι ℝ) (hL : L ≠ 0) : ∃ x, L *ᵥ x ≠ 0 := by
  by_contra h
  push_neg at h
  apply hL
  ext i j
  have := congrFun (h (Pi.single j 1)) i
  simpa [Matrix.mulVec_single_one] using this

/-- Exactness of the per-block LMI for a full block (S-lemma). -/
lemma full_iff {ι : Type*} [Fintype ι] [DecidableEq ι] {p q : ℕ} (hq : 0 < q)
    (L : Matrix (Fin p) ι ℝ) (hL : L ≠ 0) (R : Matrix (Fin q) ι ℝ)
    (Y : Matrix ι ι ℝ) (hY : Y.IsHermitian) :
    (∃ lam : ℝ, (Matrix.fromBlocks (Y - lam • (Lᵀ * L)) Rᵀ R
        (lam • (1 : Matrix (Fin q) (Fin q) ℝ))).PosSemidef) ↔
      ∀ η : Matrix (Fin p) (Fin q) ℝ, OperatorBound η 1 →
        (Y - (Lᵀ * η * R + Rᵀ * ηᵀ * L)).PosSemidef := by
  -- quadratic form of the LMI matrix
  have hquad : ∀ (lam : ℝ) (x : ι → ℝ) (ξ : Fin q → ℝ),
      Sum.elim x ξ ⬝ᵥ (Matrix.fromBlocks (Y - lam • (Lᵀ * L)) Rᵀ R
        (lam • (1 : Matrix (Fin q) (Fin q) ℝ)) *ᵥ Sum.elim x ξ) =
      x ⬝ᵥ (Y *ᵥ x) - lam * ((L *ᵥ x) ⬝ᵥ (L *ᵥ x)) + 2 * (ξ ⬝ᵥ (R *ᵥ x)) + lam * (ξ ⬝ᵥ ξ) := by
    intro lam x ξ
    rw [Matrix.fromBlocks_mulVec]
    simp only [Sum.elim_comp_inl, Sum.elim_comp_inr]
    rw [sum_elim_dot]
    rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
      ← Matrix.mulVec_mulVec, dotProduct_add, dotProduct_add, dotProduct_sub,
      dotProduct_smul, dotProduct_smul, Matrix.dotProduct_mulVec x Lᵀ,
      Matrix.dotProduct_mulVec x Rᵀ, ← Matrix.mulVec_transpose, ← Matrix.mulVec_transpose,
      Matrix.transpose_transpose, Matrix.transpose_transpose, dotProduct_comm (R *ᵥ x) ξ]
    simp only [smul_eq_mul]
    ring
  constructor
  · rintro ⟨lam, hpsd⟩ η hη
    have hlam : 0 ≤ lam := by
      have := hpsd.diag_nonneg (i := Sum.inr ⟨0, hq⟩)
      simpa [Matrix.fromBlocks] using this
    refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ ?_
    · exact hY.sub (herm_blockTerm L R η)
    · intro x
      simp only [star_trivial]
      have h0 := hpsd.dotProduct_mulVec_nonneg (Sum.elim x (-(ηᵀ *ᵥ (L *ᵥ x))))
      simp only [star_trivial] at h0
      rw [hquad] at h0
      rw [Matrix.sub_mulVec, dotProduct_sub, quad_blockTerm]
      have ht := opBound_transpose η hη (L *ᵥ x)
      have h1 := nv_sq (ηᵀ *ᵥ (L *ᵥ x))
      have h2 := nv_sq (L *ᵥ x)
      have h3 : (-(ηᵀ *ᵥ (L *ᵥ x))) ⬝ᵥ (R *ᵥ x) = -((L *ᵥ x) ⬝ᵥ (η *ᵥ (R *ᵥ x))) := by
        rw [neg_dotProduct, Matrix.mulVec_transpose, ← Matrix.dotProduct_mulVec]
      have h4 : (-(ηᵀ *ᵥ (L *ᵥ x))) ⬝ᵥ (-(ηᵀ *ᵥ (L *ᵥ x))) =
          (ηᵀ *ᵥ (L *ᵥ x)) ⬝ᵥ (ηᵀ *ᵥ (L *ᵥ x)) := by simp
      rw [h3, h4] at h0
      have h5 : (ηᵀ *ᵥ (L *ᵥ x)) ⬝ᵥ (ηᵀ *ᵥ (L *ᵥ x)) ≤ (L *ᵥ x) ⬝ᵥ (L *ᵥ x) := by
        rw [← h1, ← h2]
        exact pow_le_pow_left₀ (nv_nonneg _) ht 2
      nlinarith [mul_le_mul_of_nonneg_left h5 hlam]
  · intro hall
    have hA : (Matrix.fromBlocks (Lᵀ * L) 0 0 (-(1 : Matrix (Fin q) (Fin q) ℝ))).IsHermitian := by
      refine Matrix.IsHermitian.fromBlocks ?_ ?_ ?_
      · unfold Matrix.IsHermitian
        rw [Matrix.conjTranspose_eq_transpose_of_trivial]
        simp [Matrix.transpose_mul]
      · simp
      · simp [Matrix.IsHermitian]
    have hB : (Matrix.fromBlocks Y Rᵀ R (0 : Matrix (Fin q) (Fin q) ℝ)).IsHermitian := by
      refine Matrix.IsHermitian.fromBlocks hY ?_ ?_
      · simp [Matrix.conjTranspose_eq_transpose_of_trivial]
      · simp [Matrix.IsHermitian]
    have hfeas : ∃ z : ι ⊕ Fin q → ℝ, 0 < z ⬝ᵥ
        (Matrix.fromBlocks (Lᵀ * L) 0 0 (-(1 : Matrix (Fin q) (Fin q) ℝ)) *ᵥ z) := by
      obtain ⟨x, hx⟩ := exists_mulVec_ne L hL
      refine ⟨Sum.elim x 0, ?_⟩
      rw [Matrix.fromBlocks_mulVec]
      simp only [Sum.elim_comp_inl, Sum.elim_comp_inr]
      rw [sum_elim_dot]
      simp only [Matrix.mulVec_zero, add_zero, Matrix.zero_mulVec, zero_dotProduct]
      rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose,
        Matrix.transpose_transpose]
      have h1 := nv_sq (L *ᵥ x)
      have h2 : 0 < nv (L *ᵥ x) := by
        rw [nv, norm_pos_iff]
        intro h; apply hx
        simpa using congrArg WithLp.ofLp h
      nlinarith
    have himp : ∀ z : ι ⊕ Fin q → ℝ, 0 ≤ z ⬝ᵥ
        (Matrix.fromBlocks (Lᵀ * L) 0 0 (-(1 : Matrix (Fin q) (Fin q) ℝ)) *ᵥ z) →
        0 ≤ z ⬝ᵥ (Matrix.fromBlocks Y Rᵀ R (0 : Matrix (Fin q) (Fin q) ℝ) *ᵥ z) := by
      intro z hz
      have hz' : z = Sum.elim (z ∘ Sum.inl) (z ∘ Sum.inr) := by simp
      set x := z ∘ Sum.inl
      set ξ := z ∘ Sum.inr
      rw [hz'] at hz ⊢
      rw [Matrix.fromBlocks_mulVec] at hz ⊢
      simp only [Sum.elim_comp_inl, Sum.elim_comp_inr] at hz ⊢
      rw [sum_elim_dot] at hz ⊢
      simp only [Matrix.mulVec_zero, add_zero, zero_add, Matrix.zero_mulVec,
        Matrix.neg_mulVec, Matrix.one_mulVec, dotProduct_neg] at hz ⊢
      rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec x Lᵀ, ← Matrix.mulVec_transpose,
        Matrix.transpose_transpose] at hz
      rw [dotProduct_add, Matrix.dotProduct_mulVec x Rᵀ, ← Matrix.mulVec_transpose,
        Matrix.transpose_transpose, dotProduct_comm (R *ᵥ x) ξ]
      -- hz : 0 ≤ w⬝w - ξ⬝ξ ; goal : 0 ≤ x⬝Yx + (ξ⬝Rx + ξ⬝Rx)
      set w := L *ᵥ x with hw
      set s := w ⬝ᵥ w with hs
      let η : Matrix (Fin p) (Fin q) ℝ := Matrix.of fun i j => -(s⁻¹ * w i * ξ j)
      have hηv : ∀ v : Fin q → ℝ, η *ᵥ v = (-(s⁻¹ * (ξ ⬝ᵥ v))) • w := by
        intro v; ext i
        simp only [η, Matrix.mulVec, dotProduct, Matrix.of_apply, Pi.smul_apply, smul_eq_mul,
          Finset.mul_sum]
        rw [neg_mul, Finset.sum_mul, ← Finset.sum_neg_distrib]
        refine Finset.sum_congr rfl fun j _ => by ring
      have hnw := nv_sq w
      have hnξ := nv_sq ξ
      have hξw : nv ξ ≤ nv w := nv_le_of_dot ξ w (by linarith)
      have hb : OperatorBound η 1 := by
        intro v
        change nv (η *ᵥ v) ≤ 1 * nv v
        rw [hηv, nv_smul, abs_neg, abs_mul, abs_inv]
        have hd := abs_dot_le ξ v
        have hs0 : 0 ≤ s := by rw [hs, ← hnw]; positivity
        rw [abs_of_nonneg hs0]
        rcases eq_or_lt_of_le hs0 with h0 | hpos
        · rw [← h0]; simp [nv_nonneg]
        · have hwpos : 0 < nv w := by
            by_contra hc; push_neg at hc
            have : nv w = 0 := le_antisymm hc (nv_nonneg w)
            rw [this] at hnw; linarith
          rw [show s = nv w ^ 2 by rw [hnw]]
          have hv := nv_nonneg v
          have hξ := nv_nonneg ξ
          rw [one_mul]
          calc (nv w ^ 2)⁻¹ * |ξ ⬝ᵥ v| * nv w
              ≤ (nv w ^ 2)⁻¹ * (nv ξ * nv v) * nv w := by gcongr
            _ = nv ξ * nv v / nv w := by field_simp
            _ ≤ nv v := by
                rw [div_le_iff₀ hwpos]
                nlinarith
      have hY' := (hall η hb).dotProduct_mulVec_nonneg x
      simp only [star_trivial] at hY'
      rw [Matrix.sub_mulVec, dotProduct_sub, quad_blockTerm, hηv, dotProduct_smul,
        smul_eq_mul] at hY'
      -- (w ⬝ w) * s⁻¹ = 1 unless w = 0, in which case ξ = 0
      rcases eq_or_ne s 0 with h0 | hne
      · have hξ0 : ξ ⬝ᵥ ξ = 0 := by
          have := hnξ ▸ sq_nonneg (nv ξ)
          linarith
        have hξz : ξ = 0 := dotProduct_self_eq_zero.1 hξ0
        rw [hξz]
        rw [h0] at hY'
        simp at hY' ⊢
        linarith
      · have e1 : (L *ᵥ x) ⬝ᵥ w = s := by rw [hs, hw]
        have e2 : -(s⁻¹ * (ξ ⬝ᵥ (R *ᵥ x))) * s = -(ξ ⬝ᵥ (R *ᵥ x)) := by field_simp
        rw [e1, e2] at hY'
        linarith
    obtain ⟨lam, hlam, hpsd⟩ := s_lemma_gen _ _ hA hB hfeas himp
    refine ⟨lam, ?_⟩
    have : Matrix.fromBlocks Y Rᵀ R 0 - lam • Matrix.fromBlocks (Lᵀ * L) 0 0
        (-(1 : Matrix (Fin q) (Fin q) ℝ)) =
        Matrix.fromBlocks (Y - lam • (Lᵀ * L)) Rᵀ R (lam • (1 : Matrix (Fin q) (Fin q) ℝ)) := by
      ext i j
      rcases i with i | i <;> rcases j with j | j <;> simp
    rwa [this] at hpsd

lemma scalar_iff {ι : Type*} [Fintype ι] {p q : ℕ} (hp : p = 1) (hq : q = 1)
    (L : Matrix (Fin p) ι ℝ) (R : Matrix (Fin q) ι ℝ) (Y : Matrix ι ι ℝ)
    (hY : Y.IsHermitian) :
    ((Y - (Lᵀ * (Matrix.of (fun (_ : Fin p) (_ : Fin q) => (1 : ℝ))) * R +
        Rᵀ * (Matrix.of (fun (_ : Fin q) (_ : Fin p) => (1 : ℝ))) * L)).PosSemidef ∧
      (Y + (Lᵀ * (Matrix.of (fun (_ : Fin p) (_ : Fin q) => (1 : ℝ))) * R +
        Rᵀ * (Matrix.of (fun (_ : Fin q) (_ : Fin p) => (1 : ℝ))) * L)).PosSemidef) ↔
      ∀ η : Matrix (Fin p) (Fin q) ℝ, OperatorBound η 1 →
        (Y - (Lᵀ * η * R + Rᵀ * ηᵀ * L)).PosSemidef := by
  subst hp hq
  set J : Matrix (Fin 1) (Fin 1) ℝ := Matrix.of (fun _ _ => (1 : ℝ)) with hJ
  have hJt : Jᵀ = J := by ext i j; rfl
  have hX : ∀ c : ℝ, Lᵀ * (c • J) * R + Rᵀ * (c • J)ᵀ * L = c • (Lᵀ * J * R + Rᵀ * J * L) := by
    intro c
    rw [Matrix.transpose_smul, hJt]
    simp [Matrix.smul_mul, Matrix.mul_smul, smul_add]
  have hJv : ∀ v : Fin 1 → ℝ, J *ᵥ v = v := by
    intro v; ext i
    simp [J, Matrix.mulVec, dotProduct, Fin.sum_univ_one, Subsingleton.elim i 0]
  constructor
  · rintro ⟨hm, hp'⟩ η hη
    set c := η 0 0
    have hηc : η = c • J := by
      ext i j
      simp [J, c, Subsingleton.elim i 0, Subsingleton.elim j 0]
    have hc : c * c ≤ 1 := by
      have h := hη (fun _ => 1)
      change nv (η *ᵥ fun _ => 1) ≤ 1 * nv (fun _ : Fin 1 => (1 : ℝ)) at h
      rw [hηc, Matrix.smul_mulVec, hJv, nv_smul, one_mul] at h
      have h1 : nv (fun _ : Fin 1 => (1 : ℝ)) = 1 := by
        have := nv_sq (fun _ : Fin 1 => (1 : ℝ))
        simp [dotProduct] at this
        have h0 := nv_nonneg (fun _ : Fin 1 => (1 : ℝ))
        rcases this with h' | h'
        · exact h'
        · linarith
      rw [h1, mul_one] at h
      have := abs_mul_abs_self c
      nlinarith [abs_nonneg c]
    have hc1 : -1 ≤ c := by nlinarith
    have hc2 : c ≤ 1 := by nlinarith
    rw [hηc, hX]
    set B := Lᵀ * J * R + Rᵀ * J * L
    have : Y - c • B = ((1 + c) / 2) • (Y - B) + ((1 - c) / 2) • (Y + B) := by
      module
    rw [this]
    exact (hm.smul (by linarith)).add (hp'.smul (by linarith))
  · intro h
    have hb1 : OperatorBound J 1 := by
      intro v; rw [hJv, one_mul]
    have hb2 : OperatorBound ((-1 : ℝ) • J) 1 := by
      intro v
      change nv (((-1 : ℝ) • J) *ᵥ v) ≤ 1 * nv v
      rw [Matrix.smul_mulVec, hJv, nv_smul]; simp
    refine ⟨?_, ?_⟩
    · have := h J hb1
      rwa [hJt] at this
    · have := h _ hb2
      rw [hX] at this
      have e : Y - (-1 : ℝ) • (Lᵀ * J * R + Rᵀ * J * L) = Y + (Lᵀ * J * R + Rᵀ * J * L) := by
        rw [neg_one_smul, sub_neg_eq_add]
      rwa [e] at this

/-- Off-diagonal arrow part. -/
def off {k : ℕ} (v : Fin k → ℝ) : Matrix (Unit ⊕ Fin k) (Unit ⊕ Fin k) ℝ :=
  Matrix.fromBlocks 0 (fun _ j => v j) (fun i _ => v i) 0

lemma arrow_add_off {k : ℕ} (u v : Fin k → ℝ) (t : ℝ) :
    arrow (u + v) t = arrow u t + off v := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> simp [arrow, off, Matrix.fromBlocks]

lemma off_sum {k N : ℕ} (v : Fin N → Fin k → ℝ) : off (∑ i, v i) = ∑ i, off (v i) := by
  ext a b
  rcases a with a | a <;> rcases b with b | b <;> simp [off, Matrix.sum_apply, Matrix.fromBlocks]

lemma blockTerm_eq_off {d k p q : ℕ} (b : LSBlock d k p q) (y : Fin d → ℝ)
    (η : Matrix (Fin p) (Fin q) ℝ) :
    b.hatLᵀ * η * b.hatR y + (b.hatR y)ᵀ * ηᵀ * b.hatL = off (b.effect y η) := by
  cases b with
  | leftFixed L R =>
    ext i j
    simp only [Matrix.add_apply, Matrix.mul_apply, Matrix.transpose_apply]
    rcases i with i | i <;> rcases j with j | j <;>
      simp [LSBlock.hatL, LSBlock.hatR, LSBlock.effect, off, Matrix.mulVec,
        dotProduct, Finset.sum_mul, Finset.mul_sum, Matrix.fromBlocks]
    all_goals first
      | (refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring)
      | (rw [Finset.sum_comm]
         refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring)
  | rightFixed L R =>
    ext i j
    simp only [Matrix.add_apply, Matrix.mul_apply, Matrix.transpose_apply]
    rcases i with i | i <;> rcases j with j | j <;>
      simp [LSBlock.hatL, LSBlock.hatR, LSBlock.effect, off, Matrix.mulVec,
        dotProduct, Finset.sum_mul, Finset.mul_sum, Matrix.fromBlocks]
    all_goals first
      | (refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring)
      | (rw [Finset.sum_comm]
         refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring)

lemma hatL_ne {d k p q : ℕ} (b : LSBlock d k p q) (hb : b.Nonzero) : b.hatL ≠ 0 := by
  cases b with
  | leftFixed L R =>
    intro h; apply hb.1
    ext i j
    have := congrFun (congrFun h i) (Sum.inr j)
    simpa [LSBlock.hatL] using this
  | rightFixed L R =>
    intro h; apply hb.1
    ext i
    have := congrFun (congrFun h i) (Sum.inl ())
    simpa [LSBlock.hatL] using this

lemma sdp_iff_env {d k N : ℕ} (D : LSData d k N) (ρ : ℝ) (y : Fin d → ℝ) (τ : ℝ) :
    D.SDP ρ y τ ↔ D.Envelope ρ y τ := by
  constructor
  · rintro ⟨Y, lam, hh, hsc, hfull, harr⟩
    refine ⟨Y, hh, fun i η hη => ?_, harr⟩
    by_cases hi : i ∈ D.scalar
    · exact (scalar_iff (D.scalar_size i hi).1 (D.scalar_size i hi).2 _ _ (Y i) (hh i)).1
        (hsc i hi) η hη
    · exact (full_iff (D.q_pos i) _ (hatL_ne _ (D.nonzero i)) _ (Y i) (hh i)).1
        ⟨lam i, hfull i hi⟩ η hη
  · rintro ⟨Y, hh, hall, harr⟩
    have hex : ∀ i, ∃ l : ℝ, i ∉ D.scalar →
        (Matrix.fromBlocks
          (Y i - l • ((D.block i).hatL.transpose * (D.block i).hatL))
          ((D.block i).hatR y).transpose ((D.block i).hatR y)
          (l • (1 : Matrix (Fin (D.q i)) (Fin (D.q i)) ℝ))).PosSemidef := by
      intro i
      by_cases hi : i ∈ D.scalar
      · exact ⟨0, fun h => absurd hi h⟩
      · obtain ⟨l, hl⟩ := (full_iff (D.q_pos i) _ (hatL_ne _ (D.nonzero i)) _ (Y i) (hh i)).2
          (hall i)
        exact ⟨l, fun _ => hl⟩
    choose lam hlam using hex
    refine ⟨Y, lam, hh, fun i hi => ?_, hlam, harr⟩
    exact (scalar_iff (D.scalar_size i hi).1 (D.scalar_size i hi).2 _ _ (Y i) (hh i)).2 (hall i)

/-- Reindexing equivalence. -/
noncomputable def σ (k : ℕ) : Fin (Fintype.card (Unit ⊕ Fin k)) ≃ Unit ⊕ Fin k :=
  (Fintype.equivFin (Unit ⊕ Fin k)).symm

/-- The cube data of the least-squares instance (all blocks treated as full blocks). -/
noncomputable def cube {d k N : ℕ} (D : LSData d k N) (y : Fin d → ℝ) (τ : ℝ) :
    CubeData (Fintype.card (Unit ⊕ Fin k)) 0 N where
  B0 := (arrow (D.nominal y) τ).submatrix (σ k) (σ k)
  B := fun i => i.elim0
  symm0 := by
    refine Matrix.IsHermitian.submatrix ?_ _
    unfold Matrix.IsHermitian
    rw [Matrix.conjTranspose_eq_transpose_of_trivial]
    ext i j
    rcases i with i | i <;> rcases j with j | j <;>
      simp [arrow, Matrix.fromBlocks, Matrix.one_apply, eq_comm]
  symm := fun i => i.elim0
  rowsL := D.p
  rowsR := D.q
  posL := D.p_pos
  posR := D.q_pos
  L := fun j => (D.block j).hatL.submatrix id (σ k)
  R := fun j => ((D.block j).hatR y).submatrix id (σ k)

lemma bt_sub {k p q : ℕ} (L : Matrix (Fin p) (Unit ⊕ Fin k) ℝ)
    (R : Matrix (Fin q) (Unit ⊕ Fin k) ℝ) (η : Matrix (Fin p) (Fin q) ℝ) :
    blockTerm (L.submatrix id (σ k)) (R.submatrix id (σ k)) η =
      (Lᵀ * η * R + Rᵀ * ηᵀ * L).submatrix (σ k) (σ k) := by
  ext i j
  simp [blockTerm, Matrix.mul_apply]

lemma sum_sub {k N : ℕ} (M : Fin N → Matrix (Unit ⊕ Fin k) (Unit ⊕ Fin k) ℝ) :
    ∑ j, (M j).submatrix (σ k) (σ k) = (∑ j, M j).submatrix (σ k) (σ k) := by
  ext a b
  simp [Matrix.sum_apply]

lemma cube_robust {d k N : ℕ} (D : LSData d k N) (y : Fin d → ℝ) (τ r : ℝ) :
    (cube D y τ).Robust r ↔ D.Robust r y τ := by
  have hmat : ∀ (θ : Fin 0 → ℝ) (η : ∀ i, Matrix (Fin (D.p i)) (Fin (D.q i)) ℝ),
      (cube D y τ).B0 + ∑ i, θ i • (cube D y τ).B i +
        ∑ j, blockTerm ((cube D y τ).L j) ((cube D y τ).R j) (η j) =
      (arrow (D.nominal y + ∑ i, (D.block i).effect y (η i)) τ).submatrix (σ k) (σ k) := by
    intro θ η
    simp only [Finset.univ_eq_empty, Finset.sum_empty, add_zero]
    simp only [cube, bt_sub, blockTerm_eq_off]
    rw [sum_sub, arrow_add_off, off_sum]
    ext a b
    simp
  constructor
  · intro h η hη
    have := h (fun i => i.elim0) η (fun i => i.elim0) hη
    rw [hmat, Matrix.posSemidef_submatrix_equiv, arrow_psd] at this
    exact this
  · intro h θ η _ hη
    convert (Matrix.posSemidef_submatrix_equiv (σ k)).2 ((arrow_psd _ _).2 (h η hη)) using 1
    exact hmat θ η

lemma cube_env {d k N : ℕ} (D : LSData d k N) (y : Fin d → ℝ) (τ r : ℝ) :
    (cube D y τ).Envelope r ↔ D.Envelope r y τ := by
  constructor
  · rintro ⟨U, V, _, hV, _, hVb, hfin⟩
    refine ⟨fun j => (V j).submatrix (σ k).symm (σ k).symm, fun j => (hV j).submatrix _,
      fun i η hη => ?_, ?_⟩
    · have := hVb i η hη
      simp only [cube, bt_sub] at this
      rw [← Matrix.posSemidef_submatrix_equiv (σ k).symm] at this
      convert this using 1
      ext a b; simp
    · rw [← Matrix.posSemidef_submatrix_equiv (σ k).symm] at hfin
      convert hfin using 1
      ext a b
      simp [cube, Matrix.sum_apply]
  · rintro ⟨Y, hY, hall, hfin⟩
    refine ⟨fun i => i.elim0, fun j => (Y j).submatrix (σ k) (σ k), fun i => i.elim0,
      fun j => (hY j).submatrix _, fun i => i.elim0, fun j η hη => ?_, ?_⟩
    · have := hall j η hη
      rw [← Matrix.posSemidef_submatrix_equiv (σ k)] at this
      convert this using 1
      have hb := bt_sub (D.block j).hatL ((D.block j).hatR y) η
      show (Y j).submatrix (σ k) (σ k) - blockTerm ((D.block j).hatL.submatrix id (σ k))
        (((D.block j).hatR y).submatrix id (σ k)) η = _
      rw [hb]
      ext a b
      simp
    · rw [← Matrix.posSemidef_submatrix_equiv (σ k)] at hfin
      convert hfin using 1
      ext a b
      simp [cube, Matrix.sum_apply]

end LSSDPAux

open RobustOpt2009.CQApproximation in
theorem solution {d k N : ℕ} (_hk : 0 < k) (_hN : 0 < N)
    (D : LSData d k N) (ρ : ℝ) (hρ : 0 < ρ) (y : Fin d → ℝ) (τ : ℝ) :
    (D.SDP ρ y τ → D.Robust ρ y τ) ∧
    (¬ D.SDP ρ y τ → ¬ D.Robust ((Real.pi / 2) * ρ) y τ) ∧
    (N = 1 → (D.SDP ρ y τ ↔ D.Robust ρ y τ)) := by
  obtain ⟨ϑ, _, h2, _, _, hmc⟩ := matrix_cube
  obtain ⟨hsafe, hexact, htight⟩ :=
    hmc (Fintype.card (Unit ⊕ Fin k)) 0 N Fintype.card_pos (LSSDPAux.cube D y τ) ρ hρ
  refine ⟨fun h => ?_, fun h => ?_, fun hN1 => ?_⟩
  · rw [LSSDPAux.sdp_iff_env, ← LSSDPAux.cube_env] at h
    exact (LSSDPAux.cube_robust D y τ ρ).1 (hsafe h)
  · rw [LSSDPAux.sdp_iff_env, ← LSSDPAux.cube_env] at h
    have := htight 2 le_rfl (fun i => i.elim0) h
    rwa [h2, LSSDPAux.cube_robust] at this
  · rw [LSSDPAux.sdp_iff_env, ← LSSDPAux.cube_env, ← LSSDPAux.cube_robust]
    exact hexact (by omega)
