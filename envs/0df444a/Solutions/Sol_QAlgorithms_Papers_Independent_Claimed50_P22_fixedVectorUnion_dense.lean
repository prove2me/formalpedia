-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Claimed50.P22.fixedVectorUnion_dense
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T08:12:25.918099+00:00
-- url     : https://prove2.me/submissions/a0c5f967-7fe1-4825-8240-764bfb419dea

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P22
open QAlgorithms.Papers.Independent.Claimed50.P22

open Set Filter Topology

universe u v w z

section SubgroupFilters

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

variable {I : Type v}

variable {K : Type w} [RCLike K]

variable {H : Type z} [NormedAddCommGroup H] [InnerProductSpace K H]

theorem g67f2_fixed_near [CompleteSpace H] (N : Subgroup G)
    (pi : G →* (H ≃ₗᵢ[K] H)) (v : H) (ε : ℝ)
    (hsmall : ∀ g ∈ N, ‖pi g v - v‖ ≤ ε) :
    ∃ w : H, (∀ g ∈ N, pi g w = w) ∧ ‖w - v‖ ≤ ε := by
  letI : InnerProductSpace ℝ H := InnerProductSpace.rclikeToReal K H
  set O : Set H := {x | ∃ g ∈ N, x = pi g v} with hO
  set S : Set H := closure (convexHull ℝ O) with hS
  have hvO : v ∈ O := ⟨1, N.one_mem, by simp⟩
  have hSne : S.Nonempty := ⟨v, subset_closure (subset_convexHull ℝ O hvO)⟩
  have hSconv : Convex ℝ S := (convex_convexHull ℝ O).closure
  have hScomp : IsComplete S := isClosed_closure.isComplete
  -- real linearity of pi g
  have hlin : ∀ g : G, IsLinearMap ℝ (fun x : H => pi g x) := by
    intro g
    refine ⟨fun x y => map_add _ x y, fun r x => ?_⟩
    show pi g ((r : K) • x) = (r : K) • pi g x
    exact map_smul _ _ _
  -- invariance of S
  have hinv : ∀ g ∈ N, ∀ x ∈ S, pi g x ∈ S := by
    intro g hg
    have h1 : convexHull ℝ O ⊆ (fun x => pi g x) ⁻¹' S := by
      apply convexHull_min
      · rintro x ⟨h, hh, rfl⟩
        refine subset_closure (subset_convexHull ℝ O ⟨g * h, N.mul_mem hg hh, ?_⟩)
        simp [LinearIsometryEquiv.coe_mul]
      · exact hSconv.is_linear_preimage (hlin g)
    have h2 : IsClosed ((fun x => pi g x) ⁻¹' S) :=
      isClosed_closure.preimage (pi g).continuous
    intro x hx
    exact closure_minimal h1 h2 hx
  obtain ⟨w, hwS, hw⟩ := exists_norm_eq_iInf_of_complete_convex hSne hScomp hSconv (0 : H)
  have hchar := fun {y : H} (hy : y ∈ S) => norm_eq_iInf_iff_real_inner_le_zero hSconv (u := (0 : H)) hy
  refine ⟨w, fun g hg => ?_, ?_⟩
  · set x := pi g w
    have hxS : x ∈ S := hinv g hg w hwS
    have hxmin : ‖(0 : H) - x‖ = ⨅ y : S, ‖(0 : H) - y‖ := by
      rw [← hw]; simp [x]
    have h1 := (hchar hwS).1 hw x hxS
    have h2 := (hchar hxS).1 hxmin w hwS
    have key : ‖x - w‖ ^ 2 ≤ 0 := by
      rw [← real_inner_self_eq_norm_sq]
      have e1 : inner ℝ ((0 : H) - w) (x - w) + inner ℝ ((0 : H) - x) (w - x) =
          inner ℝ (x - w) (x - w) := by
        simp only [zero_sub, inner_neg_left, inner_sub_left, inner_sub_right, real_inner_comm w x]
        ring
      linarith
    have : ‖x - w‖ = 0 := by nlinarith [norm_nonneg (x - w)]
    exact sub_eq_zero.mp (norm_eq_zero.mp this)
  · have hball : S ⊆ Metric.closedBall v ε := by
      apply closure_minimal _ Metric.isClosed_closedBall
      apply convexHull_min _ (convex_closedBall v ε)
      rintro x ⟨g, hg, rfl⟩
      rw [Metric.mem_closedBall, dist_eq_norm]
      exact hsmall g hg
    have := hball hwS
    rwa [Metric.mem_closedBall, dist_eq_norm] at this

/-- Lemma 12.1, PDF p. 36: the union itself is dense. Every constituent
fixed-vector space is closed and G-invariant. No Lie structure is assumed. -/
theorem solution [CompleteSpace H]
    (N : I → Subgroup G) (hN : NormalSubgroupFilter N)
    (pi : G →* (H ≃ₗᵢ[K] H))
    (hContinuous : Continuous (fun p : G × H => pi p.1 p.2)) :
    (∀ i, IsClosed (FixedVectors pi (N i))) ∧
    (∀ i g v, v ∈ FixedVectors pi (N i) → pi g v ∈ FixedVectors pi (N i)) ∧
    Dense (⋃ i, FixedVectors pi (N i)) := by
  refine ⟨fun i => ?_, fun i g v hv => ?_, ?_⟩
  · have : FixedVectors pi (N i) = ⋂ g ∈ N i, {v | pi g v = v} := by
      ext v; simp [FixedVectors]
    rw [this]
    exact isClosed_biInter fun g _ => isClosed_eq (pi g).continuous continuous_id
  · intro h hh
    have hc : g⁻¹ * h * g ∈ N i := by
      simpa using (hN.2.1 i).conj_mem h hh g⁻¹
    calc pi h (pi g v) = pi (h * g) v := by rw [map_mul]; rfl
      _ = pi (g * (g⁻¹ * h * g)) v := by rw [show h * g = g * (g⁻¹ * h * g) by group]
      _ = pi g (pi (g⁻¹ * h * g) v) := by rw [map_mul]; rfl
      _ = pi g v := by rw [hv _ hc]
  · rw [Metric.dense_iff]
    intro v ε hε
    have hcont : Continuous (fun g : G => pi g v) :=
      hContinuous.comp (continuous_id.prodMk continuous_const)
    have hU : {g : G | ‖pi g v - v‖ < ε / 2} ∈ 𝓝 (1 : G) := by
      have := hcont.tendsto 1
      simp only [map_one, LinearIsometryEquiv.coe_one, id] at this
      have hb := this (Metric.ball_mem_nhds v (half_pos hε))
      filter_upwards [hb] with g hg
      simpa [dist_eq_norm] using hg
    obtain ⟨i, hi⟩ := hN.2.2.2.2 _ hU
    obtain ⟨w, hw, hwv⟩ := g67f2_fixed_near (N i) pi v (ε / 2)
      (fun g hg => (hi hg).le)
    refine ⟨w, ?_, Set.mem_iUnion.mpr ⟨i, hw⟩⟩
    rw [Metric.mem_ball, dist_eq_norm]
    linarith
