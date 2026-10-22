-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Claimed50.P22.unitaryRepresentation_decomposition
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T08:21:04.639836+00:00
-- url     : https://prove2.me/submissions/b9e3ac56-8c7c-437f-9d2b-880567611826

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

theorem g67f2_dense [CompleteSpace H]
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

theorem g67f2_fixed_in [CompleteSpace H] (N : Subgroup G)
    (pi : G →* (H ≃ₗᵢ[K] H)) (v : H) (ε : ℝ)
    (hsmall : ∀ g ∈ N, ‖pi g v - v‖ ≤ ε) (W : Submodule K H) (hWc : IsClosed (W : Set H))
    (hW : ∀ g ∈ N, pi g v ∈ W) :
    ∃ w : H, (∀ g ∈ N, pi g w = w) ∧ ‖w - v‖ ≤ ε ∧ w ∈ W := by
  letI : InnerProductSpace ℝ H := InnerProductSpace.rclikeToReal K H
  set O : Set H := {x | ∃ g ∈ N, x = pi g v} with hO
  set S : Set H := closure (convexHull ℝ O) with hS
  have hvO : v ∈ O := ⟨1, N.one_mem, by simp⟩
  have hSne : S.Nonempty := ⟨v, subset_closure (subset_convexHull ℝ O hvO)⟩
  have hSconv : Convex ℝ S := (convex_convexHull ℝ O).closure
  have hScomp : IsComplete S := isClosed_closure.isComplete
  have hlin : ∀ g : G, IsLinearMap ℝ (fun x : H => pi g x) := by
    intro g
    refine ⟨fun x y => map_add _ x y, fun r x => ?_⟩
    show pi g ((r : K) • x) = (r : K) • pi g x
    exact map_smul _ _ _
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
  have hSW : S ⊆ W := by
    apply closure_minimal _ hWc
    apply convexHull_min
    · rintro x ⟨g, hg, rfl⟩; exact hW g hg
    · intro x hx y hy a b _ _ _
      show (a : K) • x + (b : K) • y ∈ W
      exact W.add_mem (W.smul_mem _ hx) (W.smul_mem _ hy)
  obtain ⟨w, hwS, hw⟩ := exists_norm_eq_iInf_of_complete_convex hSne hScomp hSconv (0 : H)
  have hchar := fun {y : H} (hy : y ∈ S) => norm_eq_iInf_iff_real_inner_le_zero hSconv (u := (0 : H)) hy
  refine ⟨w, fun g hg => ?_, ?_, hSW hwS⟩
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

/-- Proposition 12.2, PDF p. 36. -/
theorem solution [CompleteSpace H]
    (N : I → Subgroup G) (hN : NormalSubgroupFilter N)
    (pi : G →* (H ≃ₗᵢ[K] H))
    (hContinuous : Continuous (fun p : G × H => pi p.1 p.2)) :
    ∃ (J : Type z) (S : J → Submodule K H),
      (∀ j, IsClosed (S j : Set H)) ∧
      (∀ j g v, v ∈ S j → pi g v ∈ S j) ∧
      (∀ j k, j ≠ k → ∀ v ∈ S j, ∀ w ∈ S k, inner K v w = 0) ∧
      (Dense (Submodule.span K (⋃ j, (S j : Set H)) : Set H)) ∧
      (∀ j, ∃ i, ∀ g ∈ N i, ∀ v ∈ S j, pi g v = v) := by
  classical
  obtain ⟨hcl, hfinv, _⟩ := g67f2_dense N hN pi hContinuous
  let Good : Submodule K H → Prop := fun T =>
    IsClosed (T : Set H) ∧ (∀ g v, v ∈ T → pi g v ∈ T) ∧ (∃ i, ∀ g ∈ N i, ∀ v ∈ T, pi g v = v)
  let A : Set (Set (Submodule K H)) := {F | (∀ T ∈ F, Good T) ∧
    ∀ T ∈ F, ∀ T' ∈ F, T ≠ T' → ∀ v ∈ T, ∀ w ∈ T', inner K v w = 0}
  obtain ⟨F, hFmax⟩ := zorn_subset A (by
    intro c hcA hch
    refine ⟨⋃₀ c, ⟨fun T hT => ?_, fun T hT T' hT' hne => ?_⟩, fun s hs => Set.subset_sUnion_of_mem hs⟩
    · obtain ⟨s, hs, hTs⟩ := Set.mem_sUnion.mp hT
      exact (hcA hs).1 T hTs
    · obtain ⟨s, hs, hTs⟩ := Set.mem_sUnion.mp hT
      obtain ⟨s', hs', hTs'⟩ := Set.mem_sUnion.mp hT'
      rcases hch.total hs hs' with h | h
      · exact (hcA hs').2 T (h hTs) T' hTs' hne
      · exact (hcA hs).2 T hTs T' (h hTs') hne)
  have hFA : F ∈ A := hFmax.1
  refine ⟨F, fun j => j.1, fun j => (hFA.1 j.1 j.2).1, fun j => (hFA.1 j.1 j.2).2.1,
    fun j k hjk => hFA.2 j.1 j.2 k.1 k.2 (fun h => hjk (Subtype.ext h)), ?_,
    fun j => (hFA.1 j.1 j.2).2.2⟩
  set Sp := Submodule.span K (⋃ j : F, (j.1 : Set H)) with hSp
  by_contra hnd
  have hne : Spᗮ ≠ ⊥ := by
    intro hbot
    apply hnd
    rw [Submodule.dense_iff_topologicalClosure_eq_top, ← Submodule.orthogonal_orthogonal_eq_closure,
      hbot, Submodule.bot_orthogonal_eq_top]
  obtain ⟨w, hwW, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  -- invariance of Sp and of its orthogonal
  have hSpinv : ∀ g : G, ∀ y ∈ Sp, pi g y ∈ Sp := by
    intro g y hy
    have : Sp ≤ Sp.comap (pi g).toLinearEquiv.toLinearMap := by
      rw [hSp, Submodule.span_le]
      intro x hx
      obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hx
      show pi g x ∈ Sp
      exact Submodule.subset_span (Set.mem_iUnion.mpr ⟨j, (hFA.1 j.1 j.2).2.1 g x hj⟩)
    exact this hy
  have hWinv : ∀ g : G, ∀ x ∈ Spᗮ, pi g x ∈ Spᗮ := by
    intro g x hx
    rw [Submodule.mem_orthogonal]
    intro u hu
    have e : pi g * pi g⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
    have h1 : pi g (pi g⁻¹ u) = u := congrArg (fun e' : H ≃ₗᵢ[K] H => e' u) e
    calc inner K u (pi g x) = inner K (pi g (pi g⁻¹ u)) (pi g x) := by rw [h1]
      _ = inner K (pi g⁻¹ u) x := LinearIsometryEquiv.inner_map_map _ _ _
      _ = 0 := hx _ (hSpinv g⁻¹ u hu)
  -- a nonzero fixed vector in Spᗮ
  have hcont : Continuous (fun g : G => pi g w) :=
    hContinuous.comp (continuous_id.prodMk continuous_const)
  have hwpos : 0 < ‖w‖ := norm_pos_iff.mpr hw0
  have hU : {g : G | ‖pi g w - w‖ < ‖w‖ / 2} ∈ 𝓝 (1 : G) := by
    have := hcont.tendsto 1
    simp only [map_one, LinearIsometryEquiv.coe_one, id] at this
    have hb := this (Metric.ball_mem_nhds w (half_pos hwpos))
    filter_upwards [hb] with g hg
    simpa [dist_eq_norm] using hg
  obtain ⟨i, hi⟩ := hN.2.2.2.2 _ hU
  obtain ⟨x, hxfix, hxw, hxW⟩ := g67f2_fixed_in (N i) pi w (‖w‖ / 2) (fun g hg => (hi hg).le)
    Spᗮ (Submodule.isClosed_orthogonal _) (fun g _ => hWinv g w hwW)
  have hx0 : x ≠ 0 := by
    intro h
    rw [h, zero_sub, norm_neg] at hxw
    linarith
  let Fv : Submodule K H :=
    { carrier := FixedVectors pi (N i)
      add_mem' := by
        intro a b ha hb g hg
        simp [map_add, ha g hg, hb g hg]
      zero_mem' := by intro g hg; simp
      smul_mem' := by
        intro c a ha g hg
        simp [map_smul, ha g hg] }
  let T : Submodule K H := Fv ⊓ Spᗮ
  have hxT : x ∈ T := ⟨hxfix, hxW⟩
  have hTgood : Good T := by
    refine ⟨(hcl i).inter (Submodule.isClosed_orthogonal _), fun g v hv => ⟨hfinv i g v hv.1, hWinv g v hv.2⟩,
      ⟨i, fun g hg v hv => hv.1 g hg⟩⟩
  have hTorth : ∀ T' ∈ F, ∀ v ∈ T, ∀ u ∈ T', inner K v u = 0 ∧ inner K u v = 0 := by
    intro T' hT' v hv u hu
    have huSp : u ∈ Sp := Submodule.subset_span (Set.mem_iUnion.mpr ⟨⟨T', hT'⟩, hu⟩)
    have h1 : inner K u v = 0 := hv.2 u huSp
    exact ⟨inner_eq_zero_symm.mp h1, h1⟩
  have hTnot : T ∉ F := by
    intro hTF
    have := (hTorth T hTF x hxT x hxT).1
    exact hx0 (inner_self_eq_zero.mp this)
  have hA' : insert T F ∈ A := by
    refine ⟨fun T1 hT1 => ?_, fun T1 hT1 T2 hT2 hne12 => ?_⟩
    · rcases hT1 with rfl | hT1
      · exact hTgood
      · exact hFA.1 T1 hT1
    · rcases hT1 with rfl | hT1 <;> rcases hT2 with rfl | hT2
      · exact absurd rfl hne12
      · intro v hv u hu; exact (hTorth T2 hT2 v hv u hu).1
      · intro v hv u hu; exact (hTorth T1 hT1 u hu v hv).2
      · exact hFA.2 T1 hT1 T2 hT2 hne12
  have := hFmax.2 hA' (Set.subset_insert T F)
  exact hTnot (this (Set.mem_insert T F))

end SubgroupFilters
