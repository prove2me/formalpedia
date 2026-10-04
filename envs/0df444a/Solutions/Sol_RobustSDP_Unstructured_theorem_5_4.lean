-- Prove2me | solution 1 for RobustSDP.Unstructured.theorem_5_4
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-03T00:12:28.917386+00:00
-- url     : https://prove2.me/submissions/31ac10c0-9095-4c98-a806-4a7fea657150

import Mathlib
import Definitions.Def_RobustSDP_Unstructured_Model

set_option autoImplicit false

open Matrix in
open scoped Matrix.Norms.L2Operator in
open RobustSDP.Unstructured in
lemma p6a_nsq {ι : Type*} [Fintype ι] (u : ι → ℝ) :
    ‖(WithLp.toLp 2 u : EuclideanSpace ℝ ι)‖ ^ 2 = u ⬝ᵥ u := by
  rw [EuclideanSpace.real_norm_sq_eq]
  simp [dotProduct, sq]

open Matrix in
open scoped Matrix.Norms.L2Operator in
open RobustSDP.Unstructured in
lemma p6a_cs {ι : Type*} [Fintype ι] (u z : ι → ℝ) :
    |u ⬝ᵥ z| ≤ ‖(WithLp.toLp 2 u : EuclideanSpace ℝ ι)‖ * ‖(WithLp.toLp 2 z : EuclideanSpace ℝ ι)‖ := by
  have := abs_real_inner_le_norm (WithLp.toLp 2 u : EuclideanSpace ℝ ι) (WithLp.toLp 2 z)
  rw [EuclideanSpace.inner_toLp_toLp] at this
  simpa [dotProduct_comm] using this

open Matrix in
open scoped Matrix.Norms.L2Operator in
open RobustSDP.Unstructured in
lemma p6a_opb {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (Δ : Matrix ι κ ℝ) (w : κ → ℝ) :
    ‖(WithLp.toLp 2 (Δ *ᵥ w) : EuclideanSpace ℝ ι)‖ ≤ ‖Δ‖ * ‖(WithLp.toLp 2 w : EuclideanSpace ℝ κ)‖ := by
  simpa using l2_opNorm_mulVec Δ (WithLp.toLp 2 w)

open Matrix in
open scoped Matrix.Norms.L2Operator in
open RobustSDP.Unstructured in
lemma p6a_ople {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
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
def p6a_stk {m n : ℕ} (y : Fin (m + 1) → ℝ) (u : Fin n → ℝ) : Fin (m + 1) × Fin n → ℝ :=
  fun p => y p.1 * u p.2

open Matrix in
open scoped Matrix.Norms.L2Operator in
open RobustSDP.Unstructured in
lemma p6a_stk_dot {m n : ℕ} (y : Fin (m + 1) → ℝ) (u : Fin n → ℝ) :
    p6a_stk y u ⬝ᵥ p6a_stk y u = (y ⬝ᵥ y) * (u ⬝ᵥ u) := by
  simp only [dotProduct, p6a_stk, Fintype.sum_prod_type, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

open Matrix in
open scoped Matrix.Norms.L2Operator in
open RobustSDP.Unstructured in
lemma p6a_y_dot {m : ℕ} (x : Fin m → ℝ) :
    (Fin.cons (1 : ℝ) x : Fin (m + 1) → ℝ) ⬝ᵥ (Fin.cons (1 : ℝ) x : Fin (m + 1) → ℝ)
      = ∑ i, x i ^ 2 + 1 := by
  simp [dotProduct, Fin.sum_univ_succ, sq, add_comm]

open Matrix in
open scoped Matrix.Norms.L2Operator in
open RobustSDP.Unstructured in
lemma p6a_attain {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    [Nonempty κ] (A : Matrix ι κ ℝ) :
    ∃ w : κ → ℝ, ‖(WithLp.toLp 2 w : EuclideanSpace ℝ κ)‖ = 1 ∧
      ‖(WithLp.toLp 2 (A *ᵥ w) : EuclideanSpace ℝ ι)‖ = ‖A‖ := by
  set L := (toEuclideanLin (𝕜 := ℝ) (m := ι) (n := κ)).trans LinearMap.toContinuousLinearMap A
    with hL
  have hLv : ∀ v : EuclideanSpace ℝ κ, L v = WithLp.toLp 2 (A *ᵥ WithLp.ofLp v) := by
    intro v; simp [hL, toEuclideanLin_apply]
  obtain ⟨k⟩ := ‹Nonempty κ›
  have hne : (Metric.sphere (0 : EuclideanSpace ℝ κ) 1).Nonempty :=
    ⟨EuclideanSpace.single k 1, by simp⟩
  obtain ⟨v0, hv0, hmax⟩ := (isCompact_sphere (0 : EuclideanSpace ℝ κ) 1).exists_isMaxOn hne
    (L.continuous.norm.continuousOn)
  have hv0n : ‖v0‖ = 1 := by simpa using hv0
  have hle : ‖L‖ ≤ ‖L v0‖ := by
    refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun v => ?_
    by_cases hv : v = 0
    · simp [hv]
    have hvn : 0 < ‖v‖ := norm_pos_iff.2 hv
    have hu : ‖v‖⁻¹ • v ∈ Metric.sphere (0 : EuclideanSpace ℝ κ) 1 := by
      simp [norm_smul, hvn.ne']
    have h1 := hmax hu
    simp only [Set.mem_setOf_eq, map_smul, norm_smul, norm_inv, norm_norm] at h1
    rw [mul_comm]
    calc ‖L v‖ = ‖v‖ * (‖v‖⁻¹ * ‖L v‖) := by field_simp
      _ ≤ ‖v‖ * ‖L v0‖ := by gcongr
  have hge : ‖L v0‖ ≤ ‖L‖ := by simpa [hv0n] using L.le_opNorm v0
  refine ⟨WithLp.ofLp v0, by simpa using hv0n, ?_⟩
  rw [← hLv, l2_opNorm_def]
  exact le_antisymm hge hle

open Matrix in
open scoped Matrix.Norms.L2Operator in
open RobustSDP.Unstructured in
lemma p6a_pert_eq {m p q : ℕ} (Hs : Fin (m + 1) → Matrix (Fin p) (Fin q) ℝ)
    (Δ : Matrix (Fin p) (Fin (m + 1) × Fin q) ℝ) (x : Fin m → ℝ) :
    perturbedH Hs Δ x = affineMap Hs x +
      ∑ i : Fin (m + 1), (Fin.cons (1 : ℝ) x : Fin (m + 1) → ℝ) i • block Δ i := by
  rw [perturbedH, affineMap, Fin.sum_univ_succ]
  simp [smul_add, Finset.sum_add_distrib]
  abel

open Matrix in
open scoped Matrix.Norms.L2Operator in
open RobustSDP.Unstructured in
lemma p6a_blk {m p q : ℕ} (Δ : Matrix (Fin p) (Fin (m + 1) × Fin q) ℝ)
    (y : Fin (m + 1) → ℝ) (w : Fin q → ℝ) :
    (∑ i : Fin (m + 1), y i • block Δ i) *ᵥ w = Δ *ᵥ p6a_stk y w := by
  ext a
  simp only [mulVec, dotProduct, Matrix.sum_apply, Matrix.smul_apply, block, Matrix.of_apply,
    p6a_stk, Fintype.sum_prod_type, smul_eq_mul, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun b _ => by ring

open Matrix in
open scoped Matrix.Norms.L2Operator in
open RobustSDP.Unstructured in
lemma p6a_unit {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι] (z : ι → ℝ) :
    ∃ e : ι → ℝ, ‖(WithLp.toLp 2 e : EuclideanSpace ℝ ι)‖ = 1 ∧
      z = ‖(WithLp.toLp 2 z : EuclideanSpace ℝ ι)‖ • e := by
  by_cases hz : z = 0
  · obtain ⟨k⟩ := ‹Nonempty ι›
    refine ⟨Pi.single k 1, ?_, by simp [hz]⟩
    have h := p6a_nsq (Pi.single k (1 : ℝ) : ι → ℝ)
    have hd : (Pi.single k (1 : ℝ) : ι → ℝ) ⬝ᵥ Pi.single k 1 = 1 := by simp
    rw [hd] at h
    exact (sq_eq_sq₀ (norm_nonneg _) zero_le_one).1 (by rw [h, one_pow])
  · have hn : ‖(WithLp.toLp 2 z : EuclideanSpace ℝ ι)‖ ≠ 0 := by
      rw [norm_ne_zero_iff]; intro h; apply hz
      simpa using congrArg WithLp.ofLp h
    refine ⟨‖(WithLp.toLp 2 z : EuclideanSpace ℝ ι)‖⁻¹ • z, ?_, ?_⟩
    · rw [WithLp.toLp_smul, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hn]
    · rw [smul_smul, mul_inv_cancel₀ hn, one_smul]

open Matrix in
open scoped Matrix.Norms.L2Operator in open RobustSDP.Unstructured in
theorem solution {m p q : ℕ} (hp : 0 < p) (hq : 0 < q)
    (Hs : Fin (m + 1) → Matrix (Fin p) (Fin q) ℝ) (ρ : ℝ) (hρ : 0 < ρ) (x : Fin m → ℝ) :
    IsGreatest {s : ℝ | ∃ Δ : Matrix (Fin p) (Fin (m + 1) × Fin q) ℝ, ‖Δ‖ ≤ ρ ∧
        s = ‖perturbedH Hs Δ x‖}
      (‖affineMap Hs x‖ + ρ * Real.sqrt (∑ i, x i ^ 2 + 1)) := by
  have : Nonempty (Fin p) := ⟨⟨0, hp⟩⟩
  have : Nonempty (Fin q) := ⟨⟨0, hq⟩⟩
  set y : Fin (m + 1) → ℝ := Fin.cons 1 x with hy
  set s := Real.sqrt (∑ i, x i ^ 2 + 1) with hs
  set H := affineMap Hs x with hH
  have hS : 0 < ∑ i, x i ^ 2 + 1 := by positivity
  have hs0 : 0 < s := Real.sqrt_pos.2 hS
  have hss : s ^ 2 = y ⬝ᵥ y := by rw [hy, p6a_y_dot, hs, Real.sq_sqrt hS.le]
  have hNv : ∀ u : Fin q → ℝ, ‖(WithLp.toLp 2 (p6a_stk y u) : EuclideanSpace ℝ _)‖
      = s * ‖(WithLp.toLp 2 u : EuclideanSpace ℝ _)‖ := by
    intro u
    have h1 : ‖(WithLp.toLp 2 (p6a_stk y u) : EuclideanSpace ℝ _)‖ ^ 2
        = (s * ‖(WithLp.toLp 2 u : EuclideanSpace ℝ _)‖) ^ 2 := by
      rw [p6a_nsq, p6a_stk_dot, mul_pow, p6a_nsq, hss]
    exact (sq_eq_sq₀ (norm_nonneg _) (by positivity)).1 h1
  have hkey : ∀ (Δ : Matrix (Fin p) (Fin (m + 1) × Fin q) ℝ) (w : Fin q → ℝ),
      perturbedH Hs Δ x *ᵥ w = H *ᵥ w + Δ *ᵥ p6a_stk y w := by
    intro Δ w
    rw [p6a_pert_eq, add_mulVec, p6a_blk]
  have hup : ∀ Δ : Matrix (Fin p) (Fin (m + 1) × Fin q) ℝ, ‖Δ‖ ≤ ρ →
      ‖perturbedH Hs Δ x‖ ≤ ‖H‖ + ρ * s := by
    intro Δ hΔ
    refine p6a_ople _ _ (by positivity) fun w => ?_
    rw [hkey, WithLp.toLp_add]
    have h1 := p6a_opb H w
    have h2 := p6a_opb Δ (p6a_stk y w)
    rw [hNv] at h2
    have h3 : ‖Δ‖ * (s * ‖(WithLp.toLp 2 w : EuclideanSpace ℝ _)‖)
        ≤ ρ * (s * ‖(WithLp.toLp 2 w : EuclideanSpace ℝ _)‖) := by gcongr
    calc _ ≤ _ := norm_add_le _ _
      _ ≤ ‖H‖ * ‖(WithLp.toLp 2 w : EuclideanSpace ℝ _)‖
          + ρ * (s * ‖(WithLp.toLp 2 w : EuclideanSpace ℝ _)‖) := by linarith
      _ = _ := by ring
  obtain ⟨w, hw1, hwH⟩ := p6a_attain H
  set z := H *ᵥ w with hz
  obtain ⟨e, he1, hze⟩ := p6a_unit z
  set c := ρ / s with hc
  set Δ : Matrix (Fin p) (Fin (m + 1) × Fin q) ℝ := c • vecMulVec e (p6a_stk y w) with hΔ
  have hΔw : ∀ w', Δ *ᵥ w' = (c * (p6a_stk y w ⬝ᵥ w')) • e := by
    intro w'; ext a
    simp only [hΔ, mulVec, dotProduct, Matrix.smul_apply, vecMulVec_apply, smul_eq_mul,
      Pi.smul_apply, Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun p _ => by ring
  have hc0 : 0 < c := by positivity
  have hnorm : ‖Δ‖ ≤ ρ := by
    refine p6a_ople Δ ρ hρ.le fun w' => ?_
    rw [hΔw, WithLp.toLp_smul, norm_smul, he1, Real.norm_eq_abs, abs_mul, abs_of_pos hc0, mul_one]
    have h1 := p6a_cs (p6a_stk y w) w'
    rw [hNv, hw1, mul_one] at h1
    calc c * |p6a_stk y w ⬝ᵥ w'| ≤ c * (s * ‖(WithLp.toLp 2 w' : EuclideanSpace ℝ _)‖) := by
          gcongr
      _ = ρ * ‖(WithLp.toLp 2 w' : EuclideanSpace ℝ _)‖ := by rw [hc]; field_simp
  have hww : w ⬝ᵥ w = 1 := by rw [← p6a_nsq, hw1]; norm_num
  have hPw : perturbedH Hs Δ x *ᵥ w = (‖H‖ + ρ * s) • e := by
    rw [hkey, hΔw, p6a_stk_dot, ← hss, hww, ← hz]
    conv_lhs => rw [hze]
    rw [hwH, ← add_smul]
    congr 1
    rw [hc]; field_simp
  have hlow : ‖H‖ + ρ * s ≤ ‖perturbedH Hs Δ x‖ := by
    have h1 := p6a_opb (perturbedH Hs Δ x) w
    rw [hPw, hw1, mul_one, WithLp.toLp_smul, norm_smul, he1, mul_one, Real.norm_eq_abs,
      abs_of_nonneg (by positivity)] at h1
    exact h1
  refine ⟨⟨Δ, hnorm, (le_antisymm (hup Δ hnorm) hlow).symm⟩, ?_⟩
  rintro t ⟨Δ', hΔ', rfl⟩
  exact hup Δ' hΔ'
