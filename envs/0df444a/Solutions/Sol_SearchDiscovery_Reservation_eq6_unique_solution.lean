-- Prove2me | solution 1 for SearchDiscovery.Reservation.eq6_unique_solution
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-31T09:08:40.021358+00:00
-- url     : https://prove2.me/submissions/869dd14b-02e9-4aa9-b307-abaac0f0aa7c

import Mathlib
import Definitions.Def_SearchDiscovery_Reservation_Model

open SearchDiscovery.Reservation MeasureTheory ProbabilityTheory

theorem solution (M : SDModel) (hM : M.Standing) (x : ℝ) :
    ∃! z : ℝ, M.Qs x z = 0 := by
  set μ := M.κ x with hμ
  have hint : Integrable (fun y : ℝ => y) μ :=
    (hM.memLp_κ x).integrable (by norm_num)
  have hg : ∀ z : ℝ, Integrable (fun y : ℝ => max 0 (x + y - z)) μ := by
    intro z
    have h1 : Integrable (fun y : ℝ => x + y - z) μ :=
      ((integrable_const x).add hint).sub (integrable_const z)
    exact (integrable_const (0:ℝ)).sup h1
  set f : ℝ → ℝ := fun z => ∫ y, max 0 (x + y - z) ∂μ with hf
  have hQ : ∀ z, M.Qs x z = f z - M.cs := fun z => rfl
  -- Lipschitz
  have hlip : ∀ a b : ℝ, |f a - f b| ≤ |a - b| := by
    intro a b
    rw [hf]; dsimp only
    rw [← integral_sub (hg a) (hg b)]
    calc |∫ y, (max 0 (x + y - a) - max 0 (x + y - b)) ∂μ|
        = ‖∫ y, (max 0 (x + y - a) - max 0 (x + y - b)) ∂μ‖ := rfl
      _ ≤ ∫ y, ‖max 0 (x + y - a) - max 0 (x + y - b)‖ ∂μ := norm_integral_le_integral_norm _
      _ ≤ ∫ y, |a - b| ∂μ := by
          apply integral_mono_of_nonneg (Filter.Eventually.of_forall fun _ => norm_nonneg _)
            (integrable_const _)
          refine Filter.Eventually.of_forall fun y => ?_
          simp only [Real.norm_eq_abs]
          have := abs_max_sub_max_le_max (0:ℝ) (x + y - a) 0 (x + y - b)
          calc _ ≤ max |(0:ℝ) - 0| |x + y - a - (x + y - b)| := this
            _ = |a - b| := by
                rw [sub_self, abs_zero, show x + y - a - (x + y - b) = b - a by ring, abs_sub_comm]
                exact max_eq_right (abs_nonneg _)
      _ = |a - b| := by simp
  have hcont : Continuous f := by
    refine LipschitzWith.continuous (K := 1) ?_
    refine LipschitzWith.of_dist_le_mul fun a b => ?_
    simpa [Real.dist_eq] using hlip a b
  -- lower bound: f z ≥ x + E Y - z
  have hlow : ∀ z, x + (∫ y, y ∂μ) - z ≤ f z := by
    intro z
    have : ∫ y, (x + y - z) ∂μ ≤ f z :=
      integral_mono (((integrable_const x).add hint).sub (integrable_const z)) (hg z)
        (fun y => le_max_right _ _)
    have e : ∫ y, (x + y - z) ∂μ = x + (∫ y, y ∂μ) - z := by
      have h1 : Integrable (fun y : ℝ => x + y) μ := (integrable_const x).add hint
      rw [integral_sub h1 (integrable_const z), integral_add (integrable_const x) hint]
      simp
    linarith
  -- tends to zero at top
  have htop : Filter.Tendsto f Filter.atTop (nhds 0) := by
    have := tendsto_integral_filter_of_dominated_convergence (μ := μ)
      (F := fun z y => max 0 (x + y - z)) (f := fun _ => (0:ℝ))
      (l := Filter.atTop) (bound := fun y => max 0 (x + y))
      (Filter.Eventually.of_forall fun z => (hg z).aestronglyMeasurable)
      (by
        filter_upwards [Filter.eventually_ge_atTop (0:ℝ)] with z hz
        refine Filter.Eventually.of_forall fun y => ?_
        rw [Real.norm_eq_abs, abs_of_nonneg (le_max_left _ _)]
        exact max_le_max le_rfl (by linarith))
      (by simpa using hg 0)
      (Filter.Eventually.of_forall fun y => by
        have : Filter.Tendsto (fun z : ℝ => x + y - z) Filter.atTop Filter.atBot :=
          Filter.tendsto_atBot_add_const_left _ (x + y) Filter.tendsto_neg_atTop_atBot |>.congr
            (fun z => by ring)
        refine tendsto_const_nhds.congr' ?_
        filter_upwards [this.eventually (Filter.eventually_le_atBot 0)] with z hz
        exact (max_eq_left hz).symm)
    simpa using this
  have hcs := hM.cs_pos
  -- existence
  obtain ⟨z1, hz1⟩ : ∃ z1, f z1 ≤ M.cs := by
    have := (htop.eventually (gt_mem_nhds hcs))
    obtain ⟨z, hz⟩ := this.exists
    exact ⟨z, hz.le⟩
  set z0 := min z1 (x + (∫ y, y ∂μ) - M.cs) with hz0
  have hz0le : z0 ≤ z1 := min_le_left _ _
  have hfz0 : M.cs ≤ f z0 := by
    have := hlow z0
    have : z0 ≤ x + (∫ y, y ∂μ) - M.cs := min_le_right _ _
    linarith
  have hstrict : ∀ a b, a < b → f a = f b → f b = 0 := by
    intro a b hab heq
    have hd : ∫ y, (max 0 (x + y - a) - max 0 (x + y - b)) ∂μ = 0 := by
      rw [integral_sub (hg a) (hg b)]; exact sub_eq_zero.mpr heq
    have hnn : 0 ≤ᵐ[μ] fun y => max 0 (x + y - a) - max 0 (x + y - b) :=
      Filter.Eventually.of_forall fun y => by
        simp only [Pi.zero_apply, sub_nonneg]
        exact max_le_max le_rfl (by linarith)
    have hae := (integral_eq_zero_iff_of_nonneg_ae hnn ((hg a).sub (hg b))).mp hd
    have : (fun y => max 0 (x + y - b)) =ᵐ[μ] fun _ => (0:ℝ) := by
      filter_upwards [hae] with y hy
      simp only [Pi.zero_apply] at hy
      by_contra hne
      have hpos : 0 < x + y - b := by
        by_contra h; push_neg at h; exact hne (max_eq_left h)
      rw [max_eq_right hpos.le, max_eq_right (by linarith : (0:ℝ) ≤ x + y - a)] at hy
      linarith
    show ∫ y, max 0 (x + y - b) ∂μ = 0
    rw [integral_congr_ae this]; simp
  obtain ⟨a, -, hza⟩ := intermediate_value_Icc' hz0le hcont.continuousOn ⟨hz1, hfz0⟩
  refine ⟨a, show M.Qs x a = 0 by rw [hQ, hza, sub_self], fun b hb => ?_⟩
  have ha : f a = M.cs := hza
  have hb : f b = M.cs := by have := hb; simp only [hQ, sub_eq_zero] at this; exact this
  rcases lt_trichotomy a b with h | h | h
  · have := hstrict a b h (ha.trans hb.symm); linarith
  · exact h.symm
  · have := hstrict b a h (hb.trans ha.symm); linarith

