-- Prove2me | solution 1 for RobustSDP.Unstructured.sdp_20
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-02T09:18:41.952548+00:00
-- url     : https://prove2.me/submissions/9b0fe537-8864-4680-91b7-28cd9374c183

import Mathlib
import Definitions.Def_RobustSDP_Unstructured_Model

set_option autoImplicit false

open Matrix in
open scoped Matrix.Norms.L2Operator in
open RobustSDP.Unstructured in
lemma p64_nsq {ι : Type*} [Fintype ι] (u : ι → ℝ) :
    ‖(WithLp.toLp 2 u : EuclideanSpace ℝ ι)‖ ^ 2 = u ⬝ᵥ u := by
  rw [EuclideanSpace.real_norm_sq_eq]
  simp [dotProduct, sq]

open Matrix in
open scoped Matrix.Norms.L2Operator in
open RobustSDP.Unstructured in
lemma p64_cs {ι : Type*} [Fintype ι] (u z : ι → ℝ) :
    |u ⬝ᵥ z| ≤ ‖(WithLp.toLp 2 u : EuclideanSpace ℝ ι)‖ * ‖(WithLp.toLp 2 z : EuclideanSpace ℝ ι)‖ := by
  have := abs_real_inner_le_norm (WithLp.toLp 2 u : EuclideanSpace ℝ ι) (WithLp.toLp 2 z)
  rw [EuclideanSpace.inner_toLp_toLp] at this
  simpa [dotProduct_comm] using this

open Matrix in
open scoped Matrix.Norms.L2Operator in
open RobustSDP.Unstructured in
lemma p64_opb {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (Δ : Matrix ι κ ℝ) (w : κ → ℝ) :
    ‖(WithLp.toLp 2 (Δ *ᵥ w) : EuclideanSpace ℝ ι)‖ ≤ ‖Δ‖ * ‖(WithLp.toLp 2 w : EuclideanSpace ℝ κ)‖ := by
  simpa using l2_opNorm_mulVec Δ (WithLp.toLp 2 w)

open Matrix in
open scoped Matrix.Norms.L2Operator in
open RobustSDP.Unstructured in
lemma p64_ople {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (Δ : Matrix ι κ ℝ) (K : ℝ) (hK : 0 ≤ K)
    (h : ∀ w : κ → ℝ, ‖(WithLp.toLp 2 (Δ *ᵥ w) : EuclideanSpace ℝ ι)‖ ≤ K * ‖(WithLp.toLp 2 w : EuclideanSpace ℝ κ)‖) :
    ‖Δ‖ ≤ K := by
  rw [l2_opNorm_def]
  refine ContinuousLinearMap.opNorm_le_bound _ hK fun x => ?_
  exact h (WithLp.ofLp x)

open Matrix in
open scoped Matrix.Norms.L2Operator in
open RobustSDP.Unstructured in
/-- stacked vector `v = y ⊗ u` -/
def p64_stk {m n : ℕ} (y : Fin (m + 1) → ℝ) (u : Fin n → ℝ) : Fin (m + 1) × Fin n → ℝ :=
  fun p => y p.1 * u p.2

open Matrix in
open scoped Matrix.Norms.L2Operator in
open RobustSDP.Unstructured in
lemma p64_stk_dot {m n : ℕ} (y : Fin (m + 1) → ℝ) (u : Fin n → ℝ) :
    p64_stk y u ⬝ᵥ p64_stk y u = (y ⬝ᵥ y) * (u ⬝ᵥ u) := by
  simp only [dotProduct, p64_stk, Fintype.sum_prod_type, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

open Matrix in
open scoped Matrix.Norms.L2Operator in
open RobustSDP.Unstructured in
lemma p64_y_dot {m : ℕ} (x : Fin m → ℝ) :
    (Fin.cons (1 : ℝ) x : Fin (m + 1) → ℝ) ⬝ᵥ (Fin.cons (1 : ℝ) x : Fin (m + 1) → ℝ)
      = ∑ i, x i ^ 2 + 1 := by
  simp [dotProduct, Fin.sum_univ_succ, sq, add_comm]

open Matrix in
open scoped Matrix.Norms.L2Operator in
open RobustSDP.Unstructured in
lemma p64_pert_eq {m n : ℕ} (Fs : Fin (m + 1) → Matrix (Fin n) (Fin n) ℝ)
    (Δ : Matrix (Fin n) (Fin (m + 1) × Fin n) ℝ) (x : Fin m → ℝ) :
    perturbedLMI Fs Δ x = affineMap Fs x +
      ∑ i : Fin (m + 1), (Fin.cons (1 : ℝ) x : Fin (m + 1) → ℝ) i • (block Δ i + (block Δ i)ᵀ) := by
  rw [perturbedLMI, Fin.sum_univ_succ]
  simp [add_assoc]

open Matrix in
open scoped Matrix.Norms.L2Operator in
open RobustSDP.Unstructured in
lemma p64_quad_block {m n : ℕ} (Δ : Matrix (Fin n) (Fin (m + 1) × Fin n) ℝ)
    (y : Fin (m + 1) → ℝ) (u : Fin n → ℝ) :
    u ⬝ᵥ ((∑ i : Fin (m + 1), y i • (block Δ i + (block Δ i)ᵀ)) *ᵥ u)
      = 2 * (u ⬝ᵥ (Δ *ᵥ p64_stk y u)) := by
  simp only [dotProduct, mulVec, Matrix.sum_apply, Matrix.smul_apply, Matrix.add_apply,
    Matrix.transpose_apply, block, Matrix.of_apply, p64_stk, Fintype.sum_prod_type, smul_eq_mul,
    Finset.sum_mul, Finset.mul_sum, mul_add, add_mul, Finset.sum_add_distrib]
  have h1 : ∀ a b : Fin n, ∀ i : Fin (m + 1),
      u a * (y i * Δ a (i, b) * u b) = u a * (Δ a (i, b) * (y i * u b)) := by
    intros; ring
  have h2 : (∑ a : Fin n, ∑ b : Fin n, ∑ i : Fin (m + 1), u a * (y i * Δ b (i, a) * u b))
      = ∑ a : Fin n, ∑ i : Fin (m + 1), ∑ b : Fin n, u a * (Δ a (i, b) * (y i * u b)) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun b _ => by ring
  have h3 : (∑ a : Fin n, ∑ b : Fin n, ∑ i : Fin (m + 1), u a * (y i * Δ a (i, b) * u b))
      = ∑ a : Fin n, ∑ i : Fin (m + 1), ∑ b : Fin n, u a * (Δ a (i, b) * (y i * u b)) := by
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun b _ => by ring
  rw [h2, h3]; ring_nf; simp only [Finset.sum_mul]

open Matrix in
open scoped Matrix.Norms.L2Operator in
open RobustSDP.Unstructured in
lemma p64_herm {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) (h : Mᵀ = M) : M.IsHermitian := by
  unfold IsHermitian; rw [conjTranspose_eq_transpose_of_trivial, h]


open Matrix in
open scoped Matrix.Norms.L2Operator in
open RobustSDP.Unstructured in
lemma p64_thm51 {m n : ℕ} (Fs : Fin (m + 1) → Matrix (Fin n) (Fin n) ℝ)
    (hFs : ∀ i, (Fs i).IsSymm) (ρ : ℝ) (hρ : 0 < ρ) (x : Fin m → ℝ) :
    x ∈ robustFeasibleSet Fs ρ ↔
      (affineMap Fs x -
        (2 * ρ * Real.sqrt (∑ i, x i ^ 2 + 1)) • (1 : Matrix (Fin n) (Fin n) ℝ)).PosSemidef := by
  set y : Fin (m + 1) → ℝ := Fin.cons 1 x with hy
  set s := Real.sqrt (∑ i, x i ^ 2 + 1) with hs
  have hS : 0 < ∑ i, x i ^ 2 + 1 := by positivity
  have hs0 : 0 < s := Real.sqrt_pos.2 hS
  have hss : s ^ 2 = y ⬝ᵥ y := by rw [hy, p64_y_dot, hs, Real.sq_sqrt hS.le]
  have hNv : ∀ u : Fin n → ℝ, ‖(WithLp.toLp 2 (p64_stk y u) : EuclideanSpace ℝ _)‖
      = s * ‖(WithLp.toLp 2 u : EuclideanSpace ℝ _)‖ := by
    intro u
    have h1 : ‖(WithLp.toLp 2 (p64_stk y u) : EuclideanSpace ℝ _)‖ ^ 2
        = (s * ‖(WithLp.toLp 2 u : EuclideanSpace ℝ _)‖) ^ 2 := by
      rw [p64_nsq, p64_stk_dot, mul_pow, p64_nsq, hss]
    exact (sq_eq_sq₀ (norm_nonneg _) (by positivity)).1 h1
  have hFsymm : (affineMap Fs x)ᵀ = affineMap Fs x := by
    simp [affineMap, transpose_add, transpose_sum, transpose_smul, (hFs _).eq]
  have hquad : ∀ (Δ : Matrix (Fin n) (Fin (m + 1) × Fin n) ℝ) (u : Fin n → ℝ),
      u ⬝ᵥ (perturbedLMI Fs Δ x *ᵥ u)
        = u ⬝ᵥ (affineMap Fs x *ᵥ u) + 2 * (u ⬝ᵥ (Δ *ᵥ p64_stk y u)) := by
    intro Δ u; rw [p64_pert_eq, add_mulVec, dotProduct_add, p64_quad_block]
  have hquad2 : ∀ u : Fin n → ℝ,
      u ⬝ᵥ ((affineMap Fs x - (2 * ρ * s) • (1 : Matrix (Fin n) (Fin n) ℝ)) *ᵥ u)
        = u ⬝ᵥ (affineMap Fs x *ᵥ u) - 2 * ρ * s * (u ⬝ᵥ u) := by
    intro u; simp [sub_mulVec, dotProduct_sub, smul_mulVec]
  have hpt : ∀ Δ : Matrix (Fin n) (Fin (m + 1) × Fin n) ℝ,
      (perturbedLMI Fs Δ x)ᵀ = perturbedLMI Fs Δ x := by
    intro Δ
    rw [p64_pert_eq]
    simp only [transpose_add, transpose_sum, transpose_smul, transpose_transpose, hFsymm]
    congr 1
    refine Finset.sum_congr rfl fun i _ => by rw [add_comm ((block Δ i)ᵀ)]
  constructor
  · intro hx
    refine PosSemidef.of_dotProduct_mulVec_nonneg (p64_herm _ ?_) fun u => ?_
    · simp [transpose_sub, hFsymm]
    · simp only [star_trivial]
      rw [hquad2]
      by_cases hu : u = 0
      · simp [hu]
      have hq : 0 < u ⬝ᵥ u := lt_of_le_of_ne (by rw [← p64_nsq]; positivity)
        (Ne.symm (mt dotProduct_self_eq_zero.1 hu))
      set N := ‖(WithLp.toLp 2 u : EuclideanSpace ℝ _)‖ with hN
      have hNN : N * N = u ⬝ᵥ u := by rw [← sq, hN, p64_nsq]
      set c := -ρ / (s * (u ⬝ᵥ u)) with hc
      set Δ : Matrix (Fin n) (Fin (m + 1) × Fin n) ℝ := c • vecMulVec u (p64_stk y u) with hΔ
      have hΔw : ∀ w, Δ *ᵥ w = (c * (p64_stk y u ⬝ᵥ w)) • u := by
        intro w; ext a
        simp only [hΔ, mulVec, dotProduct, Matrix.smul_apply, vecMulVec_apply, smul_eq_mul, Pi.smul_apply,
          Finset.mul_sum, Finset.sum_mul]
        refine Finset.sum_congr rfl fun p _ => by ring
      have habsc : |c| = ρ / (s * (u ⬝ᵥ u)) := by
        rw [hc, abs_div, abs_neg, abs_of_pos hρ, abs_of_pos (by positivity)]
      have hnorm : ‖Δ‖ ≤ ρ := by
        refine (p64_ople Δ (|c| * (s * N) * N) (by positivity) fun w => ?_).trans (le_of_eq ?_)
        · rw [hΔw, WithLp.toLp_smul, norm_smul, Real.norm_eq_abs, abs_mul]
          have h1 := p64_cs (p64_stk y u) w
          rw [hNv] at h1
          have h2 := mul_le_mul_of_nonneg_left h1 (mul_nonneg (abs_nonneg c) (norm_nonneg
            (WithLp.toLp 2 u : EuclideanSpace ℝ _)))
          rw [← hN] at h2 ⊢
          nlinarith [h2]
        · rw [habsc]
          calc ρ / (s * (u ⬝ᵥ u)) * (s * N) * N = ρ / (s * (u ⬝ᵥ u)) * s * (N * N) := by ring
            _ = ρ := by rw [hNN]; field_simp
      have hP := (hx Δ hnorm).dotProduct_mulVec_nonneg u
      simp only [star_trivial] at hP
      rw [hquad, hΔw, dotProduct_smul, smul_eq_mul, p64_stk_dot, ← hss] at hP
      have hcc : c * (s ^ 2 * (u ⬝ᵥ u)) * (u ⬝ᵥ u) = -(ρ * s * (u ⬝ᵥ u)) := by
        rw [hc]; field_simp
      linarith [hP, hcc]
  · intro hP Δ hΔ
    refine PosSemidef.of_dotProduct_mulVec_nonneg (p64_herm _ (hpt Δ)) fun u => ?_
    simp only [star_trivial]
    rw [hquad]
    have h0 := hP.dotProduct_mulVec_nonneg u
    simp only [star_trivial] at h0
    rw [hquad2] at h0
    have h1 := p64_cs u (Δ *ᵥ p64_stk y u)
    have h2 := p64_opb Δ (p64_stk y u)
    rw [hNv] at h2
    have hq := p64_nsq u
    set N := ‖(WithLp.toLp 2 u : EuclideanSpace ℝ _)‖ with hN
    set M := ‖(WithLp.toLp 2 (Δ *ᵥ p64_stk y u) : EuclideanSpace ℝ _)‖
    have h3 : N * M ≤ ρ * s * (u ⬝ᵥ u) := by
      calc N * M ≤ N * (‖Δ‖ * (s * N)) := mul_le_mul_of_nonneg_left h2 (norm_nonneg _)
        _ ≤ N * (ρ * (s * N)) := by gcongr
        _ = ρ * s * (u ⬝ᵥ u) := by rw [← hq]; ring
    linarith [neg_abs_le (u ⬝ᵥ (Δ *ᵥ p64_stk y u)), h1, h3]


open Matrix in
open scoped Matrix.Norms.L2Operator in
open RobustSDP.Unstructured in
lemma p64_hermg {ι : Type*} [Fintype ι] (M : Matrix ι ι ℝ) (h : Mᵀ = M) : M.IsHermitian := by
  unfold IsHermitian; rw [conjTranspose_eq_transpose_of_trivial, h]

open Matrix in
open scoped Matrix.Norms.L2Operator in
open RobustSDP.Unstructured in
lemma p64_rmul {m n : ℕ} (x : Fin m → ℝ) (u : Fin n → ℝ) :
    rMat x *ᵥ u = p64_stk (Fin.cons (1 : ℝ) x) u := by
  ext ⟨i, a⟩
  simp [rMat, mulVec, dotProduct, p64_stk, Matrix.one_apply, mul_ite]

open Matrix in
open scoped Matrix.Norms.L2Operator in
open RobustSDP.Unstructured in
lemma p64_qf {m n : ℕ} (Fs : Fin (m + 1) → Matrix (Fin n) (Fin n) ℝ) (ρ τ : ℝ) (x : Fin m → ℝ)
    (u : Fin n → ℝ) (v : Fin (m + 1) × Fin n → ℝ) :
    Sum.elim u v ⬝ᵥ (lmi20 Fs ρ τ x *ᵥ Sum.elim u v)
      = u ⬝ᵥ (affineMap Fs x *ᵥ u) - τ * (u ⬝ᵥ u)
        + 2 * ρ * (p64_stk (Fin.cons (1 : ℝ) x) u ⬝ᵥ v) + τ * (v ⬝ᵥ v) := by
  rw [lmi20, fromBlocks_mulVec, Sum.elim_comp_inl, Sum.elim_comp_inr,
    sumElim_dotProduct_sumElim]
  have h1 : u ⬝ᵥ ((rMat x)ᵀ *ᵥ v) = p64_stk (Fin.cons (1 : ℝ) x) u ⬝ᵥ v := by
    rw [dotProduct_mulVec, vecMul_transpose, p64_rmul]
  have h2 : v ⬝ᵥ (rMat x *ᵥ u) = p64_stk (Fin.cons (1 : ℝ) x) u ⬝ᵥ v := by
    rw [p64_rmul, dotProduct_comm]
  simp only [dotProduct_add, sub_mulVec, dotProduct_sub, smul_mulVec, one_mulVec,
    dotProduct_smul, smul_eq_mul]
  rw [h1, h2]
  ring

open Matrix in
open scoped Matrix.Norms.L2Operator in
open RobustSDP.Unstructured in
lemma p64_equiv {m n : ℕ} (Fs : Fin (m + 1) → Matrix (Fin n) (Fin n) ℝ)
    (hFs : ∀ i, (Fs i).IsSymm) (ρ : ℝ) (hρ : 0 < ρ) (x : Fin m → ℝ) :
    (affineMap Fs x -
        (2 * ρ * Real.sqrt (∑ i, x i ^ 2 + 1)) • (1 : Matrix (Fin n) (Fin n) ℝ)).PosSemidef ↔
      ∃ τ : ℝ, (lmi20 Fs ρ τ x).PosSemidef := by
  set y : Fin (m + 1) → ℝ := Fin.cons 1 x with hy
  set s := Real.sqrt (∑ i, x i ^ 2 + 1) with hs
  have hS : 0 < ∑ i, x i ^ 2 + 1 := by positivity
  have hs0 : 0 < s := Real.sqrt_pos.2 hS
  have hss : s ^ 2 = y ⬝ᵥ y := by rw [hy, p64_y_dot, hs, Real.sq_sqrt hS.le]
  have hSS : ∀ u : Fin n → ℝ, p64_stk y u ⬝ᵥ p64_stk y u = s ^ 2 * (u ⬝ᵥ u) := by
    intro u; rw [p64_stk_dot, hss]
  have hFsymm : (affineMap Fs x)ᵀ = affineMap Fs x := by
    simp [affineMap, transpose_add, transpose_sum, transpose_smul, (hFs _).eq]
  have hquad2 : ∀ (c : ℝ) (u : Fin n → ℝ),
      u ⬝ᵥ ((affineMap Fs x - c • (1 : Matrix (Fin n) (Fin n) ℝ)) *ᵥ u)
        = u ⬝ᵥ (affineMap Fs x *ᵥ u) - c * (u ⬝ᵥ u) := by
    intro c u; simp [sub_mulVec, dotProduct_sub, smul_mulVec]
  have hAh : ∀ c : ℝ, (affineMap Fs x - c • (1 : Matrix (Fin n) (Fin n) ℝ)).IsHermitian := by
    intro c; exact p64_herm _ (by simp [transpose_sub, hFsymm])
  have hLh : ∀ τ : ℝ, (lmi20 Fs ρ τ x).IsHermitian := by
    intro τ
    refine IsHermitian.fromBlocks (hAh τ) ?_ (p64_hermg _ (by simp))
    simp [conjTranspose_eq_transpose_of_trivial]
  constructor
  · intro hP
    refine ⟨ρ * s, PosSemidef.of_dotProduct_mulVec_nonneg (hLh _) fun w => ?_⟩
    simp only [star_trivial]
    rw [← Sum.elim_comp_inl_inr w, p64_qf]
    set u := w ∘ Sum.inl
    set v := w ∘ Sum.inr
    have h0 := hP.dotProduct_mulVec_nonneg u
    simp only [star_trivial] at h0
    rw [hquad2] at h0
    set S := p64_stk y u
    have hS2 : S ⬝ᵥ S = s ^ 2 * (u ⬝ᵥ u) := hSS u
    have hexp : (S + s • v) ⬝ᵥ (S + s • v)
        = s ^ 2 * (u ⬝ᵥ u) + 2 * s * (S ⬝ᵥ v) + s ^ 2 * (v ⬝ᵥ v) := by
      simp only [add_dotProduct, dotProduct_add, smul_dotProduct, dotProduct_smul, smul_eq_mul,
        hS2, dotProduct_comm v S]
      ring
    have hnn : 0 ≤ (S + s • v) ⬝ᵥ (S + s • v) := by rw [← p64_nsq]; positivity
    rw [hexp] at hnn
    have key : 0 ≤ s * (u ⬝ᵥ (affineMap Fs x *ᵥ u) - ρ * s * (u ⬝ᵥ u) + 2 * ρ * (S ⬝ᵥ v)
        + ρ * s * (v ⬝ᵥ v)) := by
      nlinarith [mul_nonneg hρ.le hnn, mul_nonneg hs0.le h0]
    exact (mul_nonneg_iff_of_pos_left hs0).1 key
  · rintro ⟨τ, hP⟩
    refine PosSemidef.of_dotProduct_mulVec_nonneg (hAh _) fun u => ?_
    simp only [star_trivial]
    rw [hquad2]
    set S := p64_stk y u
    have hS2 : S ⬝ᵥ S = s ^ 2 * (u ⬝ᵥ u) := hSS u
    have h0 := hP.dotProduct_mulVec_nonneg (Sum.elim u (-(1 / s) • S))
    simp only [star_trivial] at h0
    rw [p64_qf] at h0
    have e1 : S ⬝ᵥ (-(1 / s) • S) = -(s * (u ⬝ᵥ u)) := by
      rw [dotProduct_smul, smul_eq_mul, hS2]; field_simp
    have e2 : (-(1 / s) • S) ⬝ᵥ (-(1 / s) • S) = u ⬝ᵥ u := by
      rw [dotProduct_smul, smul_dotProduct, smul_eq_mul, smul_eq_mul, hS2]; field_simp
    rw [e1, e2] at h0
    linarith

open Matrix in
open scoped Matrix.Norms.L2Operator in
open RobustSDP.Unstructured in
theorem solution {m n : ℕ} (Fs : Fin (m + 1) → Matrix (Fin n) (Fin n) ℝ)
    (hFs : ∀ i, (Fs i).IsSymm) (ρ : ℝ) (hρ : 0 < ρ) (x : Fin m → ℝ) :
    x ∈ robustFeasibleSet Fs ρ ↔ ∃ τ : ℝ, (lmi20 Fs ρ τ x).PosSemidef := by
  rw [p64_thm51 Fs hFs ρ hρ x]
  exact p64_equiv Fs hFs ρ hρ x
