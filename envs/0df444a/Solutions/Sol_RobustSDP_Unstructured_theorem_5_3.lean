-- Prove2me | solution 1 for RobustSDP.Unstructured.theorem_5_3
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-02T08:57:17.929881+00:00
-- url     : https://prove2.me/submissions/87bea12c-b3ca-4d16-bd20-0a4575526aa4

import Mathlib
import Definitions.Def_RobustSDP_Unstructured_Model

set_option autoImplicit false

open Matrix in
open scoped Matrix.Norms.L2Operator in
open RobustSDP.Unstructured in
lemma p21_nsq {ι : Type*} [Fintype ι] (u : ι → ℝ) :
    ‖(WithLp.toLp 2 u : EuclideanSpace ℝ ι)‖ ^ 2 = u ⬝ᵥ u := by
  rw [EuclideanSpace.real_norm_sq_eq]
  simp [dotProduct, sq]

open Matrix in
open scoped Matrix.Norms.L2Operator in
open RobustSDP.Unstructured in
lemma p21_cs {ι : Type*} [Fintype ι] (u z : ι → ℝ) :
    |u ⬝ᵥ z| ≤ ‖(WithLp.toLp 2 u : EuclideanSpace ℝ ι)‖ * ‖(WithLp.toLp 2 z : EuclideanSpace ℝ ι)‖ := by
  have := abs_real_inner_le_norm (WithLp.toLp 2 u : EuclideanSpace ℝ ι) (WithLp.toLp 2 z)
  rw [EuclideanSpace.inner_toLp_toLp] at this
  simpa [dotProduct_comm] using this

open Matrix in
open scoped Matrix.Norms.L2Operator in
open RobustSDP.Unstructured in
lemma p21_opb {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (Δ : Matrix ι κ ℝ) (w : κ → ℝ) :
    ‖(WithLp.toLp 2 (Δ *ᵥ w) : EuclideanSpace ℝ ι)‖ ≤ ‖Δ‖ * ‖(WithLp.toLp 2 w : EuclideanSpace ℝ κ)‖ := by
  simpa using l2_opNorm_mulVec Δ (WithLp.toLp 2 w)

open Matrix in
open scoped Matrix.Norms.L2Operator in
open RobustSDP.Unstructured in
lemma p21_ople {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
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
def p21_stk {m n : ℕ} (y : Fin (m + 1) → ℝ) (u : Fin n → ℝ) : Fin (m + 1) × Fin n → ℝ :=
  fun p => y p.1 * u p.2

open Matrix in
open scoped Matrix.Norms.L2Operator in
open RobustSDP.Unstructured in
lemma p21_stk_dot {m n : ℕ} (y : Fin (m + 1) → ℝ) (u : Fin n → ℝ) :
    p21_stk y u ⬝ᵥ p21_stk y u = (y ⬝ᵥ y) * (u ⬝ᵥ u) := by
  simp only [dotProduct, p21_stk, Fintype.sum_prod_type, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

open Matrix in
open scoped Matrix.Norms.L2Operator in
open RobustSDP.Unstructured in
lemma p21_y_dot {m : ℕ} (x : Fin m → ℝ) :
    (Fin.cons (1 : ℝ) x : Fin (m + 1) → ℝ) ⬝ᵥ (Fin.cons (1 : ℝ) x : Fin (m + 1) → ℝ)
      = ∑ i, x i ^ 2 + 1 := by
  simp [dotProduct, Fin.sum_univ_succ, sq, add_comm]

open Matrix in
open scoped Matrix.Norms.L2Operator in
open RobustSDP.Unstructured in
lemma p21_pert_eq {m n : ℕ} (Fs : Fin (m + 1) → Matrix (Fin n) (Fin n) ℝ)
    (Δ : Matrix (Fin n) (Fin (m + 1) × Fin n) ℝ) (x : Fin m → ℝ) :
    perturbedLMI Fs Δ x = affineMap Fs x +
      ∑ i : Fin (m + 1), (Fin.cons (1 : ℝ) x : Fin (m + 1) → ℝ) i • (block Δ i + (block Δ i)ᵀ) := by
  rw [perturbedLMI, Fin.sum_univ_succ]
  simp [add_assoc]

open Matrix in
open scoped Matrix.Norms.L2Operator in
open RobustSDP.Unstructured in
lemma p21_quad_block {m n : ℕ} (Δ : Matrix (Fin n) (Fin (m + 1) × Fin n) ℝ)
    (y : Fin (m + 1) → ℝ) (u : Fin n → ℝ) :
    u ⬝ᵥ ((∑ i : Fin (m + 1), y i • (block Δ i + (block Δ i)ᵀ)) *ᵥ u)
      = 2 * (u ⬝ᵥ (Δ *ᵥ p21_stk y u)) := by
  simp only [dotProduct, mulVec, Matrix.sum_apply, Matrix.smul_apply, Matrix.add_apply,
    Matrix.transpose_apply, block, Matrix.of_apply, p21_stk, Fintype.sum_prod_type, smul_eq_mul,
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
lemma p21_herm {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) (h : Mᵀ = M) : M.IsHermitian := by
  unfold IsHermitian; rw [conjTranspose_eq_transpose_of_trivial, h]


open Matrix in
open scoped Matrix.Norms.L2Operator in open RobustSDP.Unstructured in
theorem solution {m n : ℕ} (Fs : Fin (m + 1) → Matrix (Fin n) (Fin n) ℝ)
    (hFs : ∀ i, (Fs i).IsSymm) (ρ : ℝ) (hρ : 0 < ρ) (x : Fin m → ℝ) (t : ℝ) :
    (∀ Δ : Matrix (Fin n) (Fin (m + 1) × Fin n) ℝ, ‖Δ‖ ≤ ρ →
        (t • (1 : Matrix (Fin n) (Fin n) ℝ) - perturbedLMI Fs Δ x).PosSemidef) ↔
      ((t - 2 * ρ * Real.sqrt (∑ i, x i ^ 2 + 1)) • (1 : Matrix (Fin n) (Fin n) ℝ) -
        affineMap Fs x).PosSemidef := by
  set y : Fin (m + 1) → ℝ := Fin.cons 1 x with hy
  set s := Real.sqrt (∑ i, x i ^ 2 + 1) with hs
  have hS : 0 < ∑ i, x i ^ 2 + 1 := by positivity
  have hs0 : 0 < s := Real.sqrt_pos.2 hS
  have hss : s ^ 2 = y ⬝ᵥ y := by rw [hy, p21_y_dot, hs, Real.sq_sqrt hS.le]
  have hNv : ∀ u : Fin n → ℝ, ‖(WithLp.toLp 2 (p21_stk y u) : EuclideanSpace ℝ _)‖
      = s * ‖(WithLp.toLp 2 u : EuclideanSpace ℝ _)‖ := by
    intro u
    have h1 : ‖(WithLp.toLp 2 (p21_stk y u) : EuclideanSpace ℝ _)‖ ^ 2
        = (s * ‖(WithLp.toLp 2 u : EuclideanSpace ℝ _)‖) ^ 2 := by
      rw [p21_nsq, p21_stk_dot, mul_pow, p21_nsq, hss]
    exact (sq_eq_sq₀ (norm_nonneg _) (by positivity)).1 h1
  have hFsymm : (affineMap Fs x)ᵀ = affineMap Fs x := by
    simp [affineMap, transpose_add, transpose_sum, transpose_smul, (hFs _).eq]
  have hquad : ∀ (Δ : Matrix (Fin n) (Fin (m + 1) × Fin n) ℝ) (u : Fin n → ℝ),
      u ⬝ᵥ ((t • (1 : Matrix (Fin n) (Fin n) ℝ) - perturbedLMI Fs Δ x) *ᵥ u)
        = t * (u ⬝ᵥ u) - u ⬝ᵥ (affineMap Fs x *ᵥ u) - 2 * (u ⬝ᵥ (Δ *ᵥ p21_stk y u)) := by
    intro Δ u
    rw [sub_mulVec, dotProduct_sub, p21_pert_eq, add_mulVec, dotProduct_add, p21_quad_block]
    simp [smul_mulVec]
    ring
  have hquad2 : ∀ u : Fin n → ℝ,
      u ⬝ᵥ (((t - 2 * ρ * s) • (1 : Matrix (Fin n) (Fin n) ℝ) - affineMap Fs x) *ᵥ u)
        = (t - 2 * ρ * s) * (u ⬝ᵥ u) - u ⬝ᵥ (affineMap Fs x *ᵥ u) := by
    intro u; simp [sub_mulVec, dotProduct_sub, smul_mulVec]
  have hpt : ∀ Δ : Matrix (Fin n) (Fin (m + 1) × Fin n) ℝ,
      (perturbedLMI Fs Δ x)ᵀ = perturbedLMI Fs Δ x := by
    intro Δ
    rw [p21_pert_eq]
    simp only [transpose_add, transpose_sum, transpose_smul, transpose_transpose, hFsymm]
    congr 1
    refine Finset.sum_congr rfl fun i _ => by rw [add_comm ((block Δ i)ᵀ)]
  constructor
  · intro hx
    refine PosSemidef.of_dotProduct_mulVec_nonneg (p21_herm _ ?_) fun u => ?_
    · simp [transpose_sub, hFsymm]
    · simp only [star_trivial]
      rw [hquad2]
      by_cases hu : u = 0
      · simp [hu]
      have hq : 0 < u ⬝ᵥ u := lt_of_le_of_ne (by rw [← p21_nsq]; positivity)
        (Ne.symm (mt dotProduct_self_eq_zero.1 hu))
      set N := ‖(WithLp.toLp 2 u : EuclideanSpace ℝ _)‖ with hN
      have hNN : N * N = u ⬝ᵥ u := by rw [← sq, hN, p21_nsq]
      set c := ρ / (s * (u ⬝ᵥ u)) with hc
      set Δ : Matrix (Fin n) (Fin (m + 1) × Fin n) ℝ := c • vecMulVec u (p21_stk y u) with hΔ
      have hΔw : ∀ w, Δ *ᵥ w = (c * (p21_stk y u ⬝ᵥ w)) • u := by
        intro w; ext a
        simp only [hΔ, mulVec, dotProduct, Matrix.smul_apply, vecMulVec_apply, smul_eq_mul, Pi.smul_apply,
          Finset.mul_sum, Finset.sum_mul]
        refine Finset.sum_congr rfl fun p _ => by ring
      have habsc : |c| = ρ / (s * (u ⬝ᵥ u)) := by
        rw [hc, abs_of_pos (by positivity)]
      have hnorm : ‖Δ‖ ≤ ρ := by
        refine (p21_ople Δ (|c| * (s * N) * N) (by positivity) fun w => ?_).trans (le_of_eq ?_)
        · rw [hΔw, WithLp.toLp_smul, norm_smul, Real.norm_eq_abs, abs_mul]
          have h1 := p21_cs (p21_stk y u) w
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
      rw [hquad, hΔw, dotProduct_smul, smul_eq_mul, p21_stk_dot, ← hss] at hP
      have hcc : c * (s ^ 2 * (u ⬝ᵥ u)) * (u ⬝ᵥ u) = ρ * s * (u ⬝ᵥ u) := by
        rw [hc]; field_simp
      nlinarith [hP, hcc]
  · intro hP Δ hΔ
    refine PosSemidef.of_dotProduct_mulVec_nonneg (p21_herm _ ?_) fun u => ?_
    · simp [transpose_sub, hpt Δ]
    simp only [star_trivial]
    rw [hquad]
    have h0 := hP.dotProduct_mulVec_nonneg u
    simp only [star_trivial] at h0
    rw [hquad2] at h0
    have h1 := p21_cs u (Δ *ᵥ p21_stk y u)
    have h2 := p21_opb Δ (p21_stk y u)
    rw [hNv] at h2
    have hq := p21_nsq u
    set N := ‖(WithLp.toLp 2 u : EuclideanSpace ℝ _)‖ with hN
    set M := ‖(WithLp.toLp 2 (Δ *ᵥ p21_stk y u) : EuclideanSpace ℝ _)‖
    have h3 : N * M ≤ ρ * s * (u ⬝ᵥ u) := by
      calc N * M ≤ N * (‖Δ‖ * (s * N)) := mul_le_mul_of_nonneg_left h2 (norm_nonneg _)
        _ ≤ N * (ρ * (s * N)) := by gcongr
        _ = ρ * s * (u ⬝ᵥ u) := by rw [← hq]; ring
    nlinarith [le_abs_self (u ⬝ᵥ (Δ *ᵥ p21_stk y u)), h1, h3]
