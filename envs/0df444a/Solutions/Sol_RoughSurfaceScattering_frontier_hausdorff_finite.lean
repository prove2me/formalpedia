-- Prove2me | solution 1 for RoughSurfaceScattering.frontier_hausdorff_finite
-- status  : ACCEPTED   (prove)
-- author  : @もち
-- created : 2026-11-24T05:23:03.620751+00:00
-- url     : https://prove2.me/submissions/fb0f7c11-337f-4695-8e03-f3ca6a051a5d

import Mathlib
import Definitions.Def_RoughSurfaceScattering_Basic

open MeasureTheory Metric
open RoughSurfaceScattering

lemma abs_coord_le_norm (v : R2) (i : Fin 2) : |v i| ≤ ‖v‖ := by
  have h := EuclideanSpace.norm_sq_eq v
  rw [Fin.sum_univ_two] at h
  have h0 : |v i| ^ 2 ≤ ‖v‖ ^ 2 := by
    rw [h, sq_abs]
    fin_cases i
    · simp only [Fin.zero_eta, Real.norm_eq_abs, sq_abs]; nlinarith [sq_nonneg (v 1)]
    · simp only [Fin.mk_one, Real.norm_eq_abs, sq_abs]; nlinarith [sq_nonneg (v 0)]
  exact (sq_le_sq₀ (abs_nonneg _) (norm_nonneg _)).mp h0

lemma continuous_coord (Q : R2 ≃ₗᵢ[ℝ] R2) (p : R2) (i : Fin 2) :
    Continuous fun x : R2 => (Q (x - p)) i :=
  (PiLp.continuous_apply 2 _ i).comp (Q.continuous.comp (continuous_id.sub continuous_const))

/-- A boundary point inside a chart lies on the graph. -/
lemma chart_on_graph (D : Set R2) (hDo : IsOpen D) (p : R2) (Q : R2 ≃ₗᵢ[ℝ] R2) (r : ℝ)
    (g : ℝ → ℝ) (hgc : Continuous g)
    (hch : ∀ x ∈ ball p r, (x ∈ D ↔ (Q (x - p)) 1 < g ((Q (x - p)) 0)))
    (y : R2) (hy : y ∈ frontier D) (hyb : y ∈ ball p r) :
    (Q (y - p)) 1 = g ((Q (y - p)) 0) := by
  have hyD : y ∉ D := by rw [hDo.frontier_eq] at hy; exact hy.2
  have h1 : g ((Q (y - p)) 0) ≤ (Q (y - p)) 1 :=
    not_lt.mp fun h => hyD ((hch y hyb).mpr h)
  refine le_antisymm ?_ h1
  by_contra hlt
  push Not at hlt
  set U := ball p r ∩ {x : R2 | g ((Q (x - p)) 0) < (Q (x - p)) 1}
  have hU : IsOpen U := isOpen_ball.inter
    (isOpen_lt (hgc.comp (continuous_coord Q p 0)) (continuous_coord Q p 1))
  obtain ⟨x, hxU, hxD⟩ := mem_closure_iff.mp (frontier_subset_closure hy) U hU ⟨hyb, hlt⟩
  exact lt_asymm hxU.2 ((hch x hxU.1).mp hxD)

lemma pt_sub (a b c d : ℝ) : pt a b - pt c d = pt (a - c) (b - d) := by
  ext i; fin_cases i <;> simp [pt]

lemma norm_pt_le (a b : ℝ) : ‖pt a b‖ ≤ |a| + |b| := by
  rw [EuclideanSpace.norm_eq]
  simp only [pt, Fin.sum_univ_two, Real.norm_eq_abs, sq_abs]
  simp only [PiLp.toLp_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
  rw [Real.sqrt_le_left (by positivity)]
  nlinarith [abs_nonneg a, abs_nonneg b, sq_abs a, sq_abs b]

lemma pt_coords (q : R2) : pt (q 0) (q 1) = q := by
  ext i; fin_cases i <;> simp [pt]

/-- The boundary piece inside one chart has finite length. -/
lemma piece_finite (lam : ℝ) (D : Set R2) (hDo : IsOpen D) (p : R2) (Q : R2 ≃ₗᵢ[ℝ] R2)
    (r : ℝ) (g : ℝ → ℝ) (hg : IsC2Lambda lam g)
    (hch : ∀ x ∈ ball p r, (x ∈ D ↔ (Q (x - p)) 1 < g ((Q (x - p)) 0))) :
    (Measure.hausdorffMeasure 1 : Measure R2) (frontier D ∩ ball p r) ≠ ⊤ := by
  set φ : ℝ → R2 := fun t => p + Q.symm (pt t (g t)) with hφ
  -- the piece is a graph over `[-r, r]`
  have hsub : frontier D ∩ ball p r ⊆ φ '' Set.Icc (-r) r := by
    rintro y ⟨hy, hyb⟩
    have hgr := chart_on_graph D hDo p Q r g hg.1.continuous hch y hy hyb
    have h0 : |(Q (y - p)) 0| < r := by
      have := abs_coord_le_norm (Q (y - p)) 0
      rw [Q.norm_map, ← dist_eq_norm] at this
      exact lt_of_le_of_lt this hyb
    refine ⟨(Q (y - p)) 0, ⟨by linarith [neg_abs_le ((Q (y - p)) 0)],
      by linarith [le_abs_self ((Q (y - p)) 0)]⟩, ?_⟩
    simp only [hφ, ← hgr, pt_coords, LinearIsometryEquiv.symm_apply_apply]
    abel
  -- `g` is Lipschitz on `[-r, r]`
  have hdc : Continuous (deriv g) := hg.1.continuous_deriv (by norm_num)
  obtain ⟨Cg, hCg⟩ := isCompact_Icc.exists_bound_of_continuousOn (s := Set.Icc (-r) r)
    hdc.continuousOn
  have hgL : LipschitzOnWith (Real.toNNReal Cg) g (Set.Icc (-r) r) := by
    refine (convex_Icc _ _).lipschitzOnWith_of_nnnorm_deriv_le
      (fun x _ => hg.1.differentiable (by norm_num) x) fun x hx => ?_
    rw [← NNReal.coe_le_coe, coe_nnnorm, Real.coe_toNNReal']
    exact (hCg x hx).trans (le_max_left _ _)
  have hφL : LipschitzOnWith (1 + Real.toNNReal Cg) φ (Set.Icc (-r) r) := by
    refine LipschitzOnWith.of_dist_le_mul fun x hx y hy => ?_
    have hgxy := hgL.dist_le_mul x hx y hy
    rw [Real.dist_eq] at hgxy ⊢
    rw [dist_eq_norm, hφ]
    simp only [add_sub_add_left_eq_sub, ← map_sub, LinearIsometryEquiv.norm_map, pt_sub]
    refine (norm_pt_le _ _).trans ?_
    push_cast
    rw [Real.dist_eq] at hgxy
    nlinarith [abs_nonneg (x - y)]
  have himg := hφL.hausdorffMeasure_image_le (d := 1) zero_le_one
  rw [hausdorffMeasure_real, Real.volume_Icc, ENNReal.rpow_one] at himg
  refine ne_top_of_le_ne_top ?_ ((measure_mono hsub).trans himg)
  exact ENNReal.mul_ne_top ENNReal.coe_ne_top ENNReal.ofReal_ne_top

theorem solution (lam : ℝ) (D : Set R2) (hD : IsC2LambdaDomain lam D) :
    (Measure.hausdorffMeasure 1 : Measure R2) (frontier D) ≠ ⊤ := by
  classical
  have hS : IsCompact (frontier D) := isCompact_of_isClosed_isBounded isClosed_frontier
    (hD.2.2.1.closure.subset frontier_subset_closure)
  choose Q r g hr hg hch using hD.2.2.2
  set U : R2 → Set R2 := fun x => if hx : x ∈ frontier D then ball x (r x hx) else Set.univ
  have hU : ∀ x ∈ frontier D, U x ∈ nhds x := by
    intro x hx
    simp only [U, dif_pos hx]
    exact ball_mem_nhds x (hr x hx)
  obtain ⟨t, ht, hcover⟩ := hS.elim_nhds_subcover U hU
  have hsub : frontier D ⊆ ⋃ x ∈ t, frontier D ∩ U x := by
    intro y hy
    obtain ⟨x, hx, hyx⟩ := Set.mem_iUnion₂.mp (hcover hy)
    exact Set.mem_iUnion₂.mpr ⟨x, hx, hy, hyx⟩
  refine ne_top_of_le_ne_top ?_ ((measure_mono hsub).trans (measure_biUnion_finset_le _ _))
  refine ENNReal.sum_ne_top.mpr fun x hx => ?_
  have hxS := ht x hx
  simp only [U, dif_pos hxS]
  exact piece_finite lam D hD.1 x (Q x hxS) (r x hxS) (g x hxS) (hg x hxS) (hch x hxS)
