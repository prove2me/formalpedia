-- Prove2me | solution 1 for Transcendence.taylor_tail_le
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-02T10:12:18.345825+00:00
-- url     : https://prove2.me/submissions/76b87a90-65cb-4541-bd22-58d1601e68ca

import Mathlib

/-!
# The tail of a Taylor series (Waldschmidt, DALAG Lemma 4.13, tail half)

On the line `w ↦ G (w • z)` the `k`-th Taylor coefficient at `0` is
`tc G k z = D^k G(0)(z, …, z) / k!` (`iteratedDeriv_line`), and the one-variable Taylor series converges at `w = 1` (`hasSum_tc`).
Cauchy's inequality on the circle of radius `R / r` bounds the `k`-th term by `M (r/R)^k`
(`norm_tc_le`), so the tail from `T` on is at most the geometric series `M (r/R)^T / (1 - r/R)`.
This replaces the book's Schwarz lemma; no completeness of `E` is needed.
-/

namespace TaylorTailLe

open Metric
open scoped Nat

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- The `k`-th Taylor coefficient at `0` of the line restriction `w ↦ G (w • z)`. -/
noncomputable def tc (G : E → ℂ) (k : ℕ) (z : E) : ℂ :=
  (k ! : ℂ)⁻¹ * iteratedFDeriv ℂ k G 0 (fun _ => z)

lemma iteratedDeriv_line {G : E → ℂ} (hG : AnalyticOnNhd ℂ G Set.univ) (z : E) (k : ℕ) :
    iteratedDeriv k (fun w : ℂ => G (w • z)) 0 = iteratedFDeriv ℂ k G 0 (fun _ => z) := by
  let g : ℂ →L[ℂ] E := (ContinuousLinearMap.id ℂ ℂ).smulRight z
  have hg : (fun w : ℂ => G (w • z)) = G ∘ g := by
    ext w; simp [g]
  have hGc : ContDiff ℂ k G := hG.contDiff
  rw [iteratedDeriv_eq_iteratedFDeriv, hg, g.iteratedFDeriv_comp_right hGc 0 le_rfl]
  simp [g]

lemma differentiable_line {G : E → ℂ} (hG : AnalyticOnNhd ℂ G Set.univ) (z : E) :
    Differentiable ℂ (fun w : ℂ => G (w • z)) := by
  have hGd : Differentiable ℂ G := fun x => (hG x (Set.mem_univ x)).differentiableAt
  exact hGd.comp (differentiable_id.smul_const z)

lemma hasSum_tc {G : E → ℂ} (hG : AnalyticOnNhd ℂ G Set.univ) (z : E) :
    HasSum (fun k => tc G k z) (G z) := by
  have h := Complex.hasSum_taylorSeries_of_entire (differentiable_line hG z) 0 1
  simp only [sub_zero, one_pow, one_smul, smul_eq_mul, one_mul] at h
  have e : (fun k => tc G k z) =
      fun n => (n ! : ℂ)⁻¹ * iteratedDeriv n (fun w : ℂ => G (w • z)) 0 := by
    funext k; rw [iteratedDeriv_line hG]; rfl
  rw [e]; exact h

lemma norm_tc_le {G : E → ℂ} (hG : AnalyticOnNhd ℂ G Set.univ) {R M s : ℝ} (hR : 0 < R)
    (hs : 0 < s) (hM : ∀ x ∈ closedBall (0 : E) R, ‖G x‖ ≤ M) {z : E} (hz : ‖z‖ ≤ s)
    (k : ℕ) : ‖tc G k z‖ ≤ M * (s / R) ^ k := by
  have hρ : 0 < R / s := div_pos hR hs
  have hC : ∀ w ∈ sphere (0 : ℂ) (R / s), ‖(fun w : ℂ => G (w • z)) w‖ ≤ M := by
    intro w hw
    apply hM
    rw [mem_closedBall, dist_zero_right, norm_smul]
    rw [mem_sphere, dist_zero_right] at hw
    rw [hw]
    calc R / s * ‖z‖ ≤ R / s * s := mul_le_mul_of_nonneg_left hz hρ.le
      _ = R := div_mul_cancel₀ R hs.ne'
  have h := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le k hρ
    (differentiable_line hG z).diffContOnCl hC
  rw [iteratedDeriv_line hG] at h
  rw [tc, norm_mul, norm_inv, Complex.norm_natCast]
  have hk : (0 : ℝ) < k ! := by exact_mod_cast Nat.factorial_pos k
  calc (k ! : ℝ)⁻¹ * ‖iteratedFDeriv ℂ k G 0 (fun _ => z)‖
      ≤ (k ! : ℝ)⁻¹ * (k ! * M / (R / s) ^ k) :=
        mul_le_mul_of_nonneg_left h (inv_nonneg.mpr hk.le)
    _ = M * (s / R) ^ k := by
        rw [div_pow, div_pow]; field_simp

end TaylorTailLe

theorem solution {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {G : E → ℂ}
    (hG : AnalyticOnNhd ℂ G Set.univ) {r R M : ℝ} (hr : 0 < r) (hrR : r < R)
    (hM : ∀ x ∈ Metric.closedBall (0 : E) R, ‖G x‖ ≤ M) {z : E} (hz : ‖z‖ ≤ r) (T : ℕ) :
    ‖G z - ∑ k ∈ Finset.range T, (k.factorial : ℂ)⁻¹ * iteratedFDeriv ℂ k G 0 (fun _ => z)‖ ≤
      M * (r / R) ^ T / (1 - r / R) := by
  have hR : 0 < R := hr.trans hrR
  have hq0 : 0 ≤ r / R := by positivity
  have hq1 : r / R < 1 := (div_lt_one hR).mpr hrR
  have hgeom : HasSum (fun k : ℕ => M * (r / R) ^ (k + T)) (M * (r / R) ^ T / (1 - r / R)) := by
    have h := (hasSum_geometric_of_lt_one hq0 hq1).mul_left (M * (r / R) ^ T)
    rw [← div_eq_mul_inv] at h
    have e : (fun k : ℕ => M * (r / R) ^ (k + T)) = fun i => M * (r / R) ^ T * (r / R) ^ i := by
      funext k; ring
    rw [e]; exact h
  exact ((hasSum_nat_add_iff' T).mpr (TaylorTailLe.hasSum_tc hG z)).norm_le_of_bounded hgeom
    fun k => TaylorTailLe.norm_tc_le hG hR hr hM hz (k + T)
