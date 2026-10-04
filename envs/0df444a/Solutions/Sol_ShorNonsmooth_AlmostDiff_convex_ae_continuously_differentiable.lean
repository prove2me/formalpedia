-- Prove2me | solution 1 for ShorNonsmooth.AlmostDiff.convex_ae_continuously_differentiable
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-03T19:00:57.733451+00:00
-- url     : https://prove2.me/submissions/9a0262c7-b9b0-4500-96b5-69c04266bd61

import Mathlib
import Definitions.Def_ShorNonsmooth_AlmostDiff_IsSubgradient
import Definitions.Def_ShorNonsmooth_AlmostDiff_AlmostDifferentiable
import Definitions.Def_ShorNonsmooth_AlmostDiff_almostGradients



namespace ShorNonsmooth.AlmostDiff

open Filter Topology Metric

lemma ad_lip {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : ConvexOn ℝ Set.univ f)
    (S : Set (EuclideanSpace ℝ (Fin n))) (hS : Bornology.IsBounded S) :
    ∃ L : NNReal, LipschitzOnWith L f S := by
  have hc : Continuous f := hf.locallyLipschitz.continuous
  obtain ⟨R, hR⟩ := hS.subset_ball (0 : EuclideanSpace ℝ (Fin n))
  have hb : Bornology.IsBounded (f '' ball (0 : EuclideanSpace ℝ (Fin n)) (R + 1)) :=
    ((isCompact_closedBall (0 : EuclideanSpace ℝ (Fin n)) (R + 1)).image hc).isBounded.subset
      (Set.image_mono ball_subset_closedBall)
  obtain ⟨K, hK⟩ := (hf.subset (Set.subset_univ _) (convex_ball _ _)).exists_lipschitzOnWith_of_isBounded
    (by linarith : R < R + 1) hb
  exact ⟨K, hK.mono hR⟩

lemma ad_ae {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : ConvexOn ℝ Set.univ f) :
    ∀ᵐ x ∂(MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin n))),
        DifferentiableAt ℝ f x := by
  have h : ∀ m : ℕ, ∀ᵐ x ∂(MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin n))),
      x ∈ ball (0 : EuclideanSpace ℝ (Fin n)) m →
        DifferentiableWithinAt ℝ f (ball (0 : EuclideanSpace ℝ (Fin n)) m) x := by
    intro m
    obtain ⟨L, hL⟩ := ad_lip f hf _ (isBounded_ball (x := (0 : EuclideanSpace ℝ (Fin n))) (r := m))
    exact hL.ae_differentiableWithinAt_of_mem
  rw [← MeasureTheory.ae_all_iff] at h
  filter_upwards [h] with x hx
  obtain ⟨m, hm⟩ := exists_nat_gt ‖x‖
  have hxm : x ∈ ball (0 : EuclideanSpace ℝ (Fin n)) m := by simpa using hm
  exact (hx m hxm).differentiableAt (isOpen_ball.mem_nhds hxm)

lemma ad_sub {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : ConvexOn ℝ Set.univ f)
    (x : EuclideanSpace ℝ (Fin n)) (hd : DifferentiableAt ℝ f x) :
    ∀ y, f y - f x ≥ inner ℝ (gradient f x) (y - x) := by
  intro y
  have hφ : ConvexOn ℝ Set.univ (f ∘ (AffineMap.lineMap x y : ℝ →ᵃ[ℝ] EuclideanSpace ℝ (Fin n))) := by
    simpa using hf.comp_affineMap (AffineMap.lineMap x y : ℝ →ᵃ[ℝ] EuclideanSpace ℝ (Fin n))
  have hd' : HasDerivAt (f ∘ (AffineMap.lineMap x y : ℝ →ᵃ[ℝ] EuclideanSpace ℝ (Fin n))) (fderiv ℝ f x (y - x)) 0 := by
    have h1 : HasDerivAt (AffineMap.lineMap x y : ℝ → EuclideanSpace ℝ (Fin n)) (y - x) 0 :=
      AffineMap.hasDerivAt_lineMap
    have h2 : HasFDerivAt f (fderiv ℝ f x) (AffineMap.lineMap x y (0 : ℝ)) := by
      simpa using hd.hasFDerivAt
    exact h2.comp_hasDerivAt (0 : ℝ) h1
  have := hφ.le_slope_of_hasDerivAt (Set.mem_univ (0 : ℝ)) (Set.mem_univ 1) one_pos hd'
  rw [slope_def_field] at this
  simp at this
  rw [gradient, InnerProductSpace.toDual_symm_apply, map_sub]
  linarith

lemma ad_uniq {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (x g : EuclideanSpace ℝ (Fin n)) (hd : DifferentiableAt ℝ f x)
    (hg : ∀ y, f y - f x ≥ inner ℝ g (y - x)) : gradient f x = g := by
  have hmin : IsLocalMin (fun y => f y - innerSL ℝ g y) x := by
    refine Filter.Eventually.of_forall (fun y => ?_)
    have := hg y
    simp only [innerSL_apply_apply, inner_sub_right] at *
    linarith
  have hD : HasFDerivAt (fun y => f y - innerSL ℝ g y) (fderiv ℝ f x - innerSL ℝ g) x :=
    hd.hasFDerivAt.sub (innerSL ℝ g).hasFDerivAt
  have h0 := hmin.hasFDerivAt_eq_zero hD
  rw [sub_eq_zero] at h0
  apply ext_inner_right ℝ
  intro v
  rw [gradient, InnerProductSpace.toDual_symm_apply, h0]
  simp

lemma ad_closed {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ) (hc : Continuous f)
    (xs gs : ℕ → EuclideanSpace ℝ (Fin n)) (x g : EuclideanSpace ℝ (Fin n))
    (hx : Tendsto xs atTop (𝓝 x)) (hg : Tendsto gs atTop (𝓝 g))
    (hs : ∀ k y, f y - f (xs k) ≥ inner ℝ (gs k) (y - xs k)) :
    ∀ y, f y - f x ≥ inner ℝ g (y - x) := by
  intro y
  have h1 : Tendsto (fun k => f y - f (xs k)) atTop (𝓝 (f y - f x)) :=
    tendsto_const_nhds.sub ((hc.tendsto x).comp hx)
  have h2 : Tendsto (fun k => inner ℝ (gs k) (y - xs k)) atTop (𝓝 (inner ℝ g (y - x))) :=
    hg.inner (tendsto_const_nhds.sub hx)
  exact le_of_tendsto_of_tendsto' h2 h1 (fun k => hs k y)

lemma ad_seq {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : ConvexOn ℝ Set.univ f)
    (xs : ℕ → EuclideanSpace ℝ (Fin n)) (x : EuclideanSpace ℝ (Fin n))
    (hx : Tendsto xs atTop (𝓝 x)) (hds : ∀ k, DifferentiableAt ℝ f (xs k))
    (hd : DifferentiableAt ℝ f x) :
    Tendsto (fun k => gradient f (xs k)) atTop (𝓝 (gradient f x)) := by
  have hc : Continuous f := hf.locallyLipschitz.continuous
  obtain ⟨R, hR⟩ := (isBounded_range_of_tendsto xs hx).subset_ball x
  obtain ⟨L, hL⟩ := ad_lip f hf (ball x (R + 1)) isBounded_ball
  have hb : ∀ k, gradient f (xs k) ∈ closedBall (0 : EuclideanSpace ℝ (Fin n)) L := by
    intro k
    have hk : xs k ∈ ball x R := hR (Set.mem_range_self k)
    have hn : ball x (R + 1) ∈ 𝓝 (xs k) := by
      apply isOpen_ball.mem_nhds
      rw [mem_ball] at hk ⊢; linarith
    have := norm_fderiv_le_of_lipschitzOn (𝕜 := ℝ) hn hL
    rw [mem_closedBall, dist_zero_right, gradient, LinearIsometryEquiv.norm_map]
    exact this
  apply tendsto_of_subseq_tendsto
  intro ns hns
  obtain ⟨a, -, φ, hφ, hlim⟩ := tendsto_subseq_of_bounded (isBounded_closedBall (x := (0 : EuclideanSpace ℝ (Fin n))) (r := (L : ℝ)))
    (x := fun k => gradient f (xs (ns k))) (fun k => hb (ns k))
  refine ⟨φ, ?_⟩
  have hx' : Tendsto (fun k => xs (ns (φ k))) atTop (𝓝 x) :=
    hx.comp (hns.comp hφ.tendsto_atTop)
  have hsub := ad_closed f hc (fun k => xs (ns (φ k))) (fun k => gradient f (xs (ns (φ k)))) x a
    hx' hlim (fun k => ad_sub f hf _ (hds _))
  rw [ad_uniq f x a hd hsub]
  exact hlim

lemma ad_cont {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : ConvexOn ℝ Set.univ f) :
    ContinuousOn (gradient f) {x | DifferentiableAt ℝ f x} := by
  intro x hx
  rw [ContinuousWithinAt, tendsto_iff_seq_tendsto]
  intro u hu
  rw [tendsto_nhdsWithin_iff] at hu
  obtain ⟨hu1, hu2⟩ := hu
  obtain ⟨N, hN⟩ := eventually_atTop.1 hu2
  rw [← tendsto_add_atTop_iff_nat N]
  have := ad_seq f hf (fun k => u (k + N)) x ((tendsto_add_atTop_iff_nat N).2 hu1)
    (fun k => hN (k + N) (by omega)) hx
  exact this

theorem ad_milestone_core {n : ℕ}
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : ConvexOn ℝ Set.univ f) :
    (∀ᵐ x ∂(MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin n))),
        DifferentiableAt ℝ f x) ∧
      ContinuousOn (gradient f) {x | DifferentiableAt ℝ f x} :=
  ⟨ad_ae f hf, ad_cont f hf⟩

theorem ad_goal_core {n : ℕ}
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : ConvexOn ℝ Set.univ f) :
    AlmostDifferentiable f ∧
      ∀ x₀ : EuclideanSpace ℝ (Fin n), ∀ g ∈ almostGradients f x₀,
        IsSubgradient f x₀ g := by
  refine ⟨⟨ad_lip f hf, ad_ae f hf, ad_cont f hf⟩, ?_⟩
  rintro x₀ g ⟨xs, hx, hds, hcl⟩
  obtain ⟨ψ, hψ, hlim⟩ := hcl.tendsto_subseq
  intro y
  exact ad_closed f hf.locallyLipschitz.continuous (fun k => xs (ψ k))
    (fun k => gradient f (xs (ψ k))) x₀ g (hx.comp hψ.tendsto_atTop) hlim
    (fun k => ad_sub f hf _ (hds _)) y

end ShorNonsmooth.AlmostDiff

open ShorNonsmooth.AlmostDiff


theorem solution {n : ℕ}
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : ConvexOn ℝ Set.univ f) :
    (∀ᵐ x ∂(MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin n))),
        DifferentiableAt ℝ f x) ∧
      ContinuousOn (gradient f) {x | DifferentiableAt ℝ f x} := by
  exact ad_milestone_core f hf
