-- Prove2me | solution 1 for RegevLWE.GaussConv.eq_11
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-02T20:36:25.257286+00:00
-- url     : https://prove2.me/submissions/c64f93a8-d690-4f97-a1da-0cf5970ae975

import Mathlib
import Definitions.Def_RegevLWE_GaussConv_Gaussian
import Definitions.Def_RegevLWE_GaussConv_Lattice

open RegevLWE.GaussConv

private lemma rho_mul_rho_completing_square {n : ℕ} (w x : EuclideanSpace ℝ (Fin n))
    {r s : ℝ} (hr : 0 < r) (hs : 0 < s) :
    let t := Real.sqrt (r ^ 2 + s ^ 2)
    rho r w * rho s (x - w) =
      rho t x * rho (r * s / t) (w - (r / t) ^ 2 • x) := by
  intro t
  unfold rho
  rw [← Real.exp_add, ← Real.exp_add]
  congr 1
  have hr_ne : r ≠ 0 := hr.ne'
  have hs_ne : s ≠ 0 := hs.ne'
  have hrs_pos : 0 < r ^ 2 + s ^ 2 := by positivity
  have hrs_ne : r ^ 2 + s ^ 2 ≠ 0 := hrs_pos.ne'
  have ht_sq : t ^ 2 = r ^ 2 + s ^ 2 := Real.sq_sqrt hrs_pos.le
  have h_rt_sq : (r / t) ^ 2 = r ^ 2 / (r ^ 2 + s ^ 2) := by
    rw [div_pow, ht_sq]
  have h_rst_sq : (r * s / t) ^ 2 = r ^ 2 * s ^ 2 / (r ^ 2 + s ^ 2) := by
    rw [div_pow, mul_pow, ht_sq]
  have h_norm1 : ‖x - w‖ ^ 2 = ‖x‖ ^ 2 - 2 * @inner ℝ _ _ x w + ‖w‖ ^ 2 :=
    norm_sub_sq_real x w
  have h_norm2 : ‖w - (r / t) ^ 2 • x‖ ^ 2 =
      ‖w‖ ^ 2 - 2 * ((r / t) ^ 2 * @inner ℝ _ _ x w) + ((r / t) ^ 2) ^ 2 * ‖x‖ ^ 2 := by
    rw [norm_sub_sq_real w ((r / t) ^ 2 • x), real_inner_smul_right, real_inner_comm x w,
      norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
  rw [h_norm1, h_norm2, h_rt_sq, h_rst_sq, ht_sq]
  field_simp
  ring

theorem solution {n : ℕ} (L : Submodule ℤ (EuclideanSpace ℝ (Fin n))) [DiscreteTopology L]
    [IsZLattice ℝ L] (u x : EuclideanSpace ℝ (Fin n)) {r s : ℝ} (hr : 0 < r) (hs : 0 < s) :
    Ydensity L u r s x =
      1 / s ^ n * rho (Real.sqrt (r ^ 2 + s ^ 2)) x *
        (rhoShiftLattice (r * s / Real.sqrt (r ^ 2 + s ^ 2))
            ((r / Real.sqrt (r ^ 2 + s ^ 2)) ^ 2 • x - u) L /
          rhoShiftLattice r (-u) L) := by
  set t := Real.sqrt (r ^ 2 + s ^ 2)
  have h_coset : rhoCoset r L u = rhoShiftLattice r (-u) L := by
    unfold rhoCoset rhoShiftLattice rhoShift
    refine tsum_congr fun v => ?_
    rw [sub_neg_eq_add]
  unfold Ydensity
  have h_term : ∀ v : L,
      discreteGaussian L u r ((v : EuclideanSpace ℝ (Fin n)) + u) *
        nu s (x - ((v : EuclideanSpace ℝ (Fin n)) + u)) =
      (1 / s ^ n * rho t x / rhoShiftLattice r (-u) L) *
        rhoShift (r * s / t) ((r / t) ^ 2 • x - u) (v : EuclideanSpace ℝ (Fin n)) := by
    intro v
    have hv_mem : ((v : EuclideanSpace ℝ (Fin n)) + u) ∈ {z : EuclideanSpace ℝ (Fin n) | z - u ∈ L} := by
      simp [add_sub_cancel_right, v.2]
    unfold discreteGaussian nu rhoShift
    rw [Set.indicator_of_mem hv_mem, h_coset]
    have h_sub : (v : EuclideanSpace ℝ (Fin n)) - ((r / t) ^ 2 • x - u) =
        ((v : EuclideanSpace ℝ (Fin n)) + u) - (r / t) ^ 2 • x := by abel
    rw [h_sub]
    have h_comp := rho_mul_rho_completing_square ((v : EuclideanSpace ℝ (Fin n)) + u) x hr hs
    dsimp only at h_comp
    calc (rho r ((v : EuclideanSpace ℝ (Fin n)) + u) / rhoShiftLattice r (-u) L) *
          (rho s (x - ((v : EuclideanSpace ℝ (Fin n)) + u)) / s ^ n)
        = (rho r ((v : EuclideanSpace ℝ (Fin n)) + u) *
            rho s (x - ((v : EuclideanSpace ℝ (Fin n)) + u))) /
            (rhoShiftLattice r (-u) L * s ^ n) := by ring
      _ = (rho t x * rho (r * s / t) (((v : EuclideanSpace ℝ (Fin n)) + u) - (r / t) ^ 2 • x)) /
            (rhoShiftLattice r (-u) L * s ^ n) := by rw [h_comp]
      _ = (1 / s ^ n * rho t x / rhoShiftLattice r (-u) L) *
            rho (r * s / t) (((v : EuclideanSpace ℝ (Fin n)) + u) - (r / t) ^ 2 • x) := by ring
  simp_rw [h_term, tsum_mul_left]
  change (1 / s ^ n * rho t x / rhoShiftLattice r (-u) L) *
      rhoShiftLattice (r * s / t) ((r / t) ^ 2 • x - u) L = _
  ring
