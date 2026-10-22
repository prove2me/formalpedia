-- Prove2me | solution 1 for QiNonsmoothEq.Damped.normFn_dirDeriv_newton
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T10:42:18.557152+00:00
-- url     : https://prove2.me/submissions/617e6b54-010a-4477-ad94-38abef800ec9

import Mathlib
import Definitions.Def_QiNonsmoothEq_Damped_Setting
set_option autoImplicit false
open Filter Topology NonsmoothNewton.Local NonsmoothNewton.Shared QiNonsmoothEq.Damped

theorem solution {n : ℕ}
    (F : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) (hF : LocallyLipschitz F)
    (y dy : EuclideanSpace ℝ (Fin n)) (hd : HasDirDerivAt F y dy (-F y)) :
    HasDirDerivAt (normFn F) y dy (-2 * normFn F y) ∧
      dirDeriv (normFn F) y dy = -2 * normFn F y := by
  have h1 : HasDirDerivAt (normFn F) y dy (-2 * normFn F y) := by
    unfold HasDirDerivAt
    have hd' : Tendsto (fun t : ℝ => t⁻¹ • (F (y + t • dy) - F y)) (𝓝[>] 0) (𝓝 (-F y)) := hd
    set q : ℝ → EuclideanSpace ℝ (Fin n) := fun t => t⁻¹ • (F (y + t • dy) - F y) with hq
    have hinner : Tendsto (fun t => inner ℝ (F y) (q t)) (𝓝[>] 0) (𝓝 (inner ℝ (F y) (-F y))) :=
      (tendsto_const_nhds (x := F y)).inner hd'
    have hnorm : Tendsto (fun t : ℝ => t / 2 * ‖q t‖ ^ 2) (𝓝[>] 0) (𝓝 (0 / 2 * ‖-F y‖ ^ 2)) := by
      have h0 : Tendsto (fun t : ℝ => t / 2) (𝓝[>] 0) (𝓝 (0 / 2)) :=
        (tendsto_id.div_const 2).mono_left nhdsWithin_le_nhds
      exact h0.mul ((hd'.norm).pow 2)
    have hsum := hinner.add hnorm
    have hlim : inner ℝ (F y) (-F y) + 0 / 2 * ‖-F y‖ ^ 2 = -2 * normFn F y := by
      unfold normFn
      simp [inner_neg_right]
    rw [hlim] at hsum
    refine hsum.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with t ht
    have ht' : t ≠ 0 := ne_of_gt ht
    have hFt : F (y + t • dy) = F y + t • q t := by
      rw [hq]; simp only
      rw [smul_smul, mul_inv_cancel₀ ht', one_smul]; abel
    simp only [normFn]
    rw [hFt]
    rw [smul_eq_mul]
    have : ‖F y + t • q t‖ ^ 2 = ‖F y‖ ^ 2 + 2 * t * inner ℝ (F y) (q t) + t ^ 2 * ‖q t‖ ^ 2 := by
      rw [norm_add_sq_real, inner_smul_right, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
      ring
    rw [this]
    field_simp
    ring
  refine ⟨h1, ?_⟩
  exact h1.limUnder_eq
