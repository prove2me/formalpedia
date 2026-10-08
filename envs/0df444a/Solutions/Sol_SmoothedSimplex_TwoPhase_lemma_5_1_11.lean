-- Prove2me | solution 1 for SmoothedSimplex.TwoPhase.lemma_5_1_11
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-05T11:00:36.76232+00:00
-- url     : https://prove2.me/submissions/3e2ab626-874c-43e5-af4b-cf7de446dc27

import Mathlib
import Definitions.Def_SmoothedSimplex_TwoPhase_kappaZero
import Definitions.Def_SmoothedSimplex_TwoPhase_shadowBoundD

set_option autoImplicit false

open SmoothedSimplex.TwoPhase in
theorem e7de0136_key {d : ℕ} (a : Fin d → Point d) (u : EuclideanSpace ℝ (Fin d)) (j : Fin d) :
    |u j| * height a (Finset.univ.erase j) j ≤ ‖∑ i : Fin d, (u i) • a i‖ := by
  classical
  set S : Submodule ℝ (Point d) :=
    Submodule.span ℝ (Set.range (fun i : (Finset.univ.erase j : Finset (Fin d)) => a i.1)) with hS
  set s : Point d := ∑ i ∈ Finset.univ.erase j, u i • a i with hs
  have hsmem : s ∈ S := by
    refine Submodule.sum_mem _ (fun i hi => Submodule.smul_mem _ _ ?_)
    exact Submodule.subset_span ⟨⟨i, hi⟩, rfl⟩
  have hsum : ∑ i : Fin d, (u i) • a i = u j • a j + s := by
    rw [hs]; exact (Finset.add_sum_erase _ (fun i => u i • a i) (Finset.mem_univ j)).symm
  rw [hsum]
  by_cases hu : u j = 0
  · rw [hu, abs_zero, zero_mul]; exact norm_nonneg _
  · have hmem : -(u j)⁻¹ • s ∈ (S : Set (Point d)) := S.smul_mem _ hsmem
    have h1 : height a (Finset.univ.erase j) j ≤ dist (a j) (-(u j)⁻¹ • s) :=
      Metric.infDist_le_dist_of_mem hmem
    have h2 : dist (a j) (-(u j)⁻¹ • s) = |u j|⁻¹ * ‖u j • a j + s‖ := by
      rw [dist_eq_norm, neg_smul, sub_neg_eq_add]
      have : a j + (u j)⁻¹ • s = (u j)⁻¹ • (u j • a j + s) := by
        rw [smul_add, smul_smul, inv_mul_cancel₀ hu, one_smul]
      rw [this, norm_smul, Real.norm_eq_abs, abs_inv]
    have hpos : 0 < |u j| := abs_pos.mpr hu
    calc |u j| * height a (Finset.univ.erase j) j
        ≤ |u j| * (|u j|⁻¹ * ‖u j • a j + s‖) := by
          rw [← h2]; exact mul_le_mul_of_nonneg_left h1 hpos.le
      _ = ‖u j • a j + s‖ := by field_simp

open SmoothedSimplex.TwoPhase in
theorem solution {d : ℕ} (a : Fin d → Point d)
    (hd : 3 ≤ d) (u : EuclideanSpace ℝ (Fin d)) (j : Fin d) (κ h : ℝ)
    (hκ : 0 < κ) (hh : 0 < h) (hu : ‖u‖ = 1)
    (hsmall : ‖∑ i : Fin d, (u i) • a i‖ ≤ κ)
    (hheight : h < height a (Finset.univ.erase j) j) :
    |u j| < κ / h := by
  have key := e7de0136_key a u j
  rw [lt_div_iff₀ hh]
  rcases (abs_nonneg (u j)).eq_or_lt with h0 | hpos
  · rw [← h0, zero_mul]; exact hκ
  · calc |u j| * h < |u j| * height a (Finset.univ.erase j) j :=
          mul_lt_mul_of_pos_left hheight hpos
      _ ≤ _ := key
      _ ≤ κ := hsmall
