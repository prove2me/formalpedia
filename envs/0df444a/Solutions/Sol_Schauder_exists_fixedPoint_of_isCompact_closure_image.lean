-- Prove2me | solution 1 for Schauder.exists_fixedPoint_of_isCompact_closure_image
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-04T17:59:12.276826+00:00
-- url     : https://prove2.me/submissions/7deda1b7-c9d6-404b-8c91-af0e84bb343b

import Mathlib
import Theorems.Thm_AGT_brouwer_fixed_point

open Metric Set Filter Topology

theorem solution {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] {G : Set E} (hGc : IsClosed G) (hGconv : Convex ℝ G)
    (hGne : G.Nonempty) (T : E → E) (hT : ContinuousOn T G) (hTG : Set.MapsTo T G G)
    (hpre : IsCompact (closure (T '' G))) : ∃ x ∈ G, T x = x := by
  classical
  set K := closure (T '' G) with hKdef
  have hKG : K ⊆ G := closure_minimal hTG.image_subset hGc
  have hTK : ∀ x ∈ G, T x ∈ K := fun x hx => subset_closure (mem_image_of_mem T hx)
  /- approximate fixed points via Schauder projections and Brouwer -/
  have happrox : ∀ ε > 0, ∃ x ∈ G, dist (T x) x ≤ ε := by
    intro ε hε
    obtain ⟨t, htK, htfin, hcover⟩ := finite_approx_of_totallyBounded hpre.totallyBounded ε hε
    set F := htfin.toFinset with hF
    let μ : E → E → ℝ := fun k x => max 0 (ε - ‖x - k‖)
    let s : E → ℝ := fun x => ∑ k ∈ F, μ k x
    let P : E → E := fun x => F.centerMass (fun k => μ k x) id
    have hμnn : ∀ k x, 0 ≤ μ k x := fun k x => le_max_left _ _
    have hs_pos : ∀ x ∈ K, 0 < s x := by
      intro x hx
      have := hcover hx
      simp only [mem_iUnion, mem_ball] at this
      obtain ⟨k, hk, hxk⟩ := this
      refine Finset.sum_pos' (fun k _ => hμnn k x) ⟨k, by simpa [hF] using hk, ?_⟩
      simp only [μ]
      rw [dist_eq_norm] at hxk
      exact lt_max_of_lt_right (by linarith)
    have hP_hull : ∀ x, 0 < s x → P x ∈ convexHull ℝ t := by
      intro x hx
      refine Finset.centerMass_mem_convexHull F (fun k _ => hμnn k x) hx ?_
      intro k hk
      simpa [hF] using hk
    have hP_close : ∀ x ∈ K, dist (P x) x ≤ ε := by
      intro x hx
      have hPx : P x = (F.filter fun k => μ k x ≠ 0).centerMass (fun k => μ k x) id :=
        (Finset.centerMass_filter_ne_zero _).symm
      have hmem : P x ∈ closedBall x ε := by
        rw [hPx]
        refine (convex_closedBall x ε).centerMass_mem (fun k _ => hμnn k x) ?_ ?_
        · rw [Finset.sum_filter_ne_zero]; exact hs_pos x hx
        · intro k hk
          rw [Finset.mem_filter] at hk
          have h2 := hk.2
          simp only [μ, ne_eq] at h2
          rw [mem_closedBall, dist_eq_norm, ← norm_neg, neg_sub]
          by_contra hc
          push Not at hc
          simp only [id_eq] at hc
          exact h2 (max_eq_left (by linarith))
      exact hmem
    have hμc : ∀ k, Continuous (μ k) := fun k =>
      continuous_const.max (continuous_const.sub ((continuous_id.sub continuous_const).norm))
    have hs_c : Continuous s := continuous_finsetSum _ fun k _ => hμc k
    have hP_cont : ∀ x, 0 < s x → ContinuousAt P x := by
      intro x hx
      have : P = fun y => (s y)⁻¹ • ∑ k ∈ F, μ k y • k := by
        funext y; simp [P, Finset.centerMass, s]
      rw [this]
      exact ((hs_c.continuousAt).inv₀ hx.ne').smul
        (continuous_finsetSum _ fun k _ => (hμc k).smul continuous_const).continuousAt
    -- the finite-dimensional subspace
    let V := Submodule.span ℝ t
    haveI : FiniteDimensional ℝ V := FiniteDimensional.span_of_finite ℝ htfin
    have hPspan : ∀ x, P x ∈ V := by
      intro x
      simp only [P, Finset.centerMass]
      refine V.smul_mem _ (V.sum_mem fun k hk => V.smul_mem _ (Submodule.subset_span ?_))
      simpa [hF] using hk
    have hhullG : convexHull ℝ t ⊆ G := convexHull_min (htK.trans hKG) hGconv
    let C : Set V := (Subtype.val : V → E) ⁻¹' convexHull ℝ t
    have hCconv : Convex ℝ C := by
      intro a ha b hb p q hp hq hpq
      show ((p • a + q • b : V) : E) ∈ convexHull ℝ t
      simp only [Submodule.coe_add, Submodule.coe_smul]
      exact (convex_convexHull ℝ t) ha hb hp hq hpq
    have hVc : IsClosed (V : Set E) := Submodule.closed_of_finiteDimensional V
    have hhc : IsCompact (convexHull ℝ t) := htfin.isCompact_convexHull ℝ
    have hCcpt : IsCompact C :=
      (hVc.isClosedEmbedding_subtypeVal).isCompact_preimage hhc
    have hCne : C.Nonempty := by
      obtain ⟨x0, hx0⟩ := hGne
      have hTx0 := hTK x0 hx0
      have := hcover hTx0
      simp only [mem_iUnion] at this
      obtain ⟨k, hk, -⟩ := this
      exact ⟨⟨k, Submodule.subset_span hk⟩, subset_convexHull ℝ t hk⟩
    let g : V → V := fun v => ⟨P (T v), hPspan _⟩
    have hgC : MapsTo g C C := by
      intro v hv
      exact hP_hull _ (hs_pos _ (hTK _ (hhullG hv)))
    have hgcont : ContinuousOn g C := by
      rw [Topology.IsInducing.subtypeVal.continuousOn_iff]
      intro v hv
      have hvG : (v : E) ∈ G := hhullG hv
      have h1 : ContinuousWithinAt (fun u : V => T u) C v :=
        (hT _ hvG).comp continuous_subtype_val.continuousWithinAt
          (fun u hu => hhullG hu)
      exact ContinuousAt.comp_continuousWithinAt (f := fun u : V => T u) (hP_cont _ (hs_pos _ (hTK _ hvG))) h1
    obtain ⟨v, hvC, hgv⟩ := AGT.brouwer_fixed_point hCconv hCcpt hCne g hgcont hgC
    have hPv : P (T v) = v := congrArg Subtype.val hgv
    refine ⟨v, hhullG hvC, ?_⟩
    have := hP_close _ (hTK _ (hhullG hvC))
    rw [hPv, dist_comm] at this
    exact this
  /- pass to the limit -/
  choose x hxG hxd using fun n : ℕ => happrox (1 / ((n : ℝ) + 1)) (by positivity)
  obtain ⟨y, hyK, φ, hφ, hlim⟩ := hpre.tendsto_subseq (fun n => hTK (x n) (hxG n))
  have hyG : y ∈ G := hKG hyK
  have hd : Tendsto (fun n => dist (T (x (φ n))) (x (φ n))) atTop (𝓝 0) := by
    refine squeeze_zero (fun n => dist_nonneg) (fun n => hxd (φ n)) ?_
    exact tendsto_one_div_add_atTop_nhds_zero_nat.comp hφ.tendsto_atTop
  have hxlim : Tendsto (fun n => x (φ n)) atTop (𝓝 y) := hlim.congr_dist hd
  have hTlim : Tendsto (fun n => T (x (φ n))) atTop (𝓝 (T y)) :=
    (hT y hyG).tendsto.comp (tendsto_nhdsWithin_iff.mpr
      ⟨hxlim, Eventually.of_forall fun n => hxG (φ n)⟩)
  exact ⟨y, hyG, tendsto_nhds_unique hTlim hlim⟩
