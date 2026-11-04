-- Prove2me | solution 1 for StrictCQ.CAKKT.limNormal_subset_polar_linCone
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-04T00:46:28.81689+00:00
-- url     : https://prove2.me/submissions/f77a931c-c0cc-483f-87b1-31cf10ae5714

import Mathlib
import Definitions.Def_StrictCQ_CAKKT_Setting
import Definitions.Def_StrictCQ_CAKKT_Conditions
import Theorems.Thm_StrictCQ_CAKKT_lemma_6_2
import Theorems.Thm_StrictCQ_CAKKT_regNormal_eq_polar_tangentCone

open Filter Topology
open scoped InnerProductSpace
open StrictCQ.CAKKT

theorem solution {n m p : ℕ} (C : Constraints n m p) (hC : C.IsC1)
    {xs : EuclideanSpace ℝ (Fin n)} (hxs : xs ∈ C.feasible) (hreg : C.CAKKTRegular xs) :
    limNormal C.feasible xs ⊆ StrictCQ.AGP.polar (C.linCone xs) := by
  rintro y ⟨z, v, hzS, hz, hv, hvN⟩
  -- Step 1: each `v k` lies in the polar of the tangent cone at `z k`; apply Lemma 6.2.
  have hvT : ∀ k, v k ∈ StrictCQ.AGP.polar (tangentCone C.feasible (z k)) := fun k => by
    rw [← regNormal_eq_polar_tangentCone C.feasible (hzS k)]; exact hvN k
  have h62 := fun k => lemma_6_2 C hC (hzS k) (hvT k)
  choose x lam mu c hmu hc hx hω hprop hr using h62
  -- Step 2: diagonal choice.
  have hsel : ∀ k : ℕ, ∃ l, dist (x k l) (z k) < 1 / ((k:ℝ) + 1) ∧
      dist (∑ i, lam k l i • gradient (C.h i) (x k l) +
        ∑ j, mu k l j • gradient (C.g j) (x k l)) (v k) < 1 / ((k:ℝ) + 1) ∧
      dist (∑ i, |lam k l i * C.h i (x k l)| + ∑ j, |mu k l j * C.g j (x k l)|) 0
        < 1 / ((k:ℝ) + 1) := by
    intro k
    have hpos : (0:ℝ) < 1 / ((k:ℝ) + 1) := by positivity
    exact (((hx k).eventually (Metric.ball_mem_nhds _ hpos)).and
      (((hω k).eventually (Metric.ball_mem_nhds _ hpos)).and
        ((hr k).eventually (Metric.ball_mem_nhds _ hpos)))).exists
  choose l hl1 hl2 hl3 using hsel
  set X : ℕ → EuclideanSpace ℝ (Fin n) := fun k => x k (l k) with hX
  set W : ℕ → EuclideanSpace ℝ (Fin n) := fun k =>
    ∑ i, lam k (l k) i • gradient (C.h i) (X k) + ∑ j, mu k (l k) j • gradient (C.g j) (X k)
    with hW
  set R : ℕ → ℝ := fun k =>
    ∑ i, |lam k (l k) i * C.h i (X k)| + ∑ j, |mu k (l k) j * C.g j (X k)| with hR
  have hinv : Tendsto (fun k : ℕ => 1 / ((k:ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hXt : Tendsto X atTop (𝓝 xs) := by
    have h1 : Tendsto (fun k => dist (X k) (z k)) atTop (𝓝 0) :=
      squeeze_zero (fun _ => dist_nonneg) (fun k => (hl1 k).le) hinv
    refine tendsto_iff_dist_tendsto_zero.2 ?_
    refine squeeze_zero (fun _ => dist_nonneg) (fun k => dist_triangle _ (z k) _) ?_
    simpa using h1.add (tendsto_iff_dist_tendsto_zero.1 hz)
  have hWt : Tendsto W atTop (𝓝 y) := by
    have h1 : Tendsto (fun k => dist (W k) (v k)) atTop (𝓝 0) :=
      squeeze_zero (fun _ => dist_nonneg) (fun k => (hl2 k).le) hinv
    refine tendsto_iff_dist_tendsto_zero.2 ?_
    refine squeeze_zero (fun _ => dist_nonneg) (fun k => dist_triangle _ (v k) _) ?_
    simpa using h1.add (tendsto_iff_dist_tendsto_zero.1 hv)
  have hRt : Tendsto R atTop (𝓝 0) := by
    refine tendsto_iff_dist_tendsto_zero.2 ?_
    exact squeeze_zero (fun _ => dist_nonneg) (fun k => (hl3 k).le) hinv
  have hR0 : ∀ k, 0 ≤ R k := fun k => by
    simp only [hR]; positivity
  -- Step 3: eventually the inactive multipliers vanish.
  have hinact : ∀ᶠ k in atTop, ∀ j, C.g j xs ≠ 0 → C.g j (X k) < 0 := by
    rw [eventually_all]
    intro j
    by_cases hj : C.g j xs = 0
    · exact Eventually.of_forall fun _ h => absurd hj h
    · have hneg : C.g j xs < 0 := lt_of_le_of_ne (hxs.2 j) hj
      have hcont : Tendsto (fun k => C.g j (X k)) atTop (𝓝 (C.g j xs)) :=
        ((hC.2 j).continuous.tendsto xs).comp hXt
      exact (hcont.eventually (gt_mem_nhds hneg)).mono fun _ h _ => h
  obtain ⟨N, hN⟩ := eventually_atTop.1 hinact
  -- Step 4: CAKKT-regularity.
  have hmem : y ∈ C.KC xs xs 0 := by
    apply hreg
    refine ⟨fun k => (X (k + N), R (k + N)), fun k => W (k + N), fun k => hR0 _, ?_, ?_, ?_⟩
    · have h1 := hXt.comp (tendsto_add_atTop_nat N)
      have h2 := hRt.comp (tendsto_add_atTop_nat N)
      exact h1.prodMk_nhds h2
    · exact hWt.comp (tendsto_add_atTop_nat N)
    · intro k
      refine ⟨lam (k + N) (l (k + N)), mu (k + N) (l (k + N)), fun j => hmu _ _ j, ?_, le_rfl, rfl⟩
      intro j hj
      rw [hprop]
      have := hN (k + N) (by omega) j hj
      have : max 0 (C.g j (X (k + N))) = 0 := max_eq_left this.le
      simp only [hX] at this
      rw [this, mul_zero]
  -- Step 5: `K_C(xs, 0) ⊆ L_Ω(xs)°`.
  obtain ⟨la, mu', hmu', hmu0, -, rfl⟩ := hmem
  intro d hd
  rw [inner_add_left, sum_inner, sum_inner]
  have h1 : ∑ i, ⟪la i • gradient (C.h i) xs, d⟫_ℝ = 0 := by
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [inner_smul_left, hd.1 i]; simp
  have h2 : ∑ j, ⟪mu' j • gradient (C.g j) xs, d⟫_ℝ ≤ 0 := by
    refine Finset.sum_nonpos fun j _ => ?_
    rw [real_inner_smul_left]
    by_cases hj : C.g j xs = 0
    · exact mul_nonpos_of_nonneg_of_nonpos (hmu' j) (hd.2 j hj)
    · simp [hmu0 j hj]
  linarith
