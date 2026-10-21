-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Renew46.P33.compatibleNet_infiniteExponent_strongLimit
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T00:35:30.1701+00:00
-- url     : https://prove2.me/submissions/e383e50b-99c7-4f18-8c3c-3c43abd0145a

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P33
open Filter

open scoped Topology

open QAlgorithms.Papers.Independent.Renew46.P33

theorem solution
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (M : VonNeumannAlgebra H)
    {I : Type*} [PartialOrder I] [Nonempty I] [IsDirectedOrder I]
    (xi proj : I → H →L[ℂ] H)
    (hxi : ∀ i, xi i ∈ M)
    (hproj : ∀ i, proj i ∈ M ∧ IsStarProjection (proj i))
    (hsupport : ∀ i, xi i = xi i * proj i)
    (hcompat : ∀ i j, i < j → xi j * proj i = xi i)
    (C : ℝ) (hbound : ∀ i, ‖xi i‖ ≤ C) :
    ∃ limit : H →L[ℂ] H,
      limit ∈ M ∧ ‖limit‖ ≤ C ∧
      (∀ v : H, Tendsto (fun i => xi i v) atTop (𝓝 (limit v))) ∧
      (∀ i, xi i = limit * proj i) := by
  have hle : ∀ i j, i ≤ j → xi j * proj i = xi i := by
    intro i j hij
    rcases hij.lt_or_eq with h | h
    · exact hcompat i j h
    · subst h; exact (hsupport i).symm
  have hle' : ∀ i j, i ≤ j → ∀ z, xi j (proj i z) = xi i z := by
    intro i j hij z
    have := congrArg (fun T => T z) (hle i j hij)
    simpa using this
  have hC0 : 0 ≤ C := le_trans (norm_nonneg _) (hbound (Classical.arbitrary I))
  set S : Submodule ℂ H := Submodule.span ℂ (⋃ i, Set.range (proj i)) with hS
  set K : Submodule ℂ H := S.topologicalClosure with hK
  haveI : CompleteSpace K := (S.isClosed_topologicalClosure).completeSpace_coe
  -- eventually constant on the span
  have hspan : ∀ y ∈ S, ∃ i0, ∀ j, i0 ≤ j → xi j y = xi i0 y := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨i, z, rfl⟩ := Set.mem_iUnion.1 hx
      refine ⟨i, fun j hj => ?_⟩
      rw [hle' i j hj z, hle' i i le_rfl z]
    | zero => exact ⟨Classical.arbitrary I, fun j _ => by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨i1, h1⟩ := hx
      obtain ⟨i2, h2⟩ := hy
      obtain ⟨i3, h13, h23⟩ := directed_of (· ≤ ·) i1 i2
      refine ⟨i3, fun j hj => ?_⟩
      rw [map_add, map_add, h1 j (h13.trans hj), h2 j (h23.trans hj), h1 i3 h13, h2 i3 h23]
    | smul c x _ hx =>
      obtain ⟨i1, h1⟩ := hx
      exact ⟨i1, fun j hj => by rw [map_smul, map_smul, h1 j hj]⟩
  -- the orthogonal complement is killed
  have hperp : ∀ u ∈ Kᗮ, ∀ j, proj j u = 0 := by
    intro u hu j
    have hmem : proj j u ∈ K :=
      S.le_topologicalClosure (Submodule.subset_span (Set.mem_iUnion.2 ⟨j, u, rfl⟩))
    have h0 : inner ℂ u (proj j u) = 0 := (Submodule.mem_orthogonal' K u).1 hu _ hmem
    have hsa := (hproj j).2.isSelfAdjoint
    have hid := (hproj j).2.isIdempotentElem
    have : inner ℂ (proj j u) (proj j u) = 0 := by
      rw [← ContinuousLinearMap.adjoint_inner_right, ← ContinuousLinearMap.star_eq_adjoint,
        hsa.star_eq]
      have : proj j (proj j u) = proj j u := by
        have := congrArg (fun T => T u) hid; simpa using this
      rw [this, h0]
    exact inner_self_eq_zero.1 this
  -- Cauchy property
  have hconv : ∀ v : H, ∃ w, Tendsto (fun i => xi i v) atTop (𝓝 w) := by
    intro v
    obtain ⟨y, hy, u, hu, rfl⟩ := K.exists_add_mem_mem_orthogonal v
    have hxu : ∀ j, xi j u = 0 := by
      intro j
      have := congrArg (fun T => T u) (hsupport j)
      simp only [ContinuousLinearMap.mul_apply] at this
      rw [this, hperp u hu j, map_zero]
    simp only [map_add, hxu, add_zero]
    refine cauchy_map_iff_exists_tendsto.1 ?_
    rw [Metric.cauchy_iff]
    refine ⟨inferInstance, fun ε hε => ?_⟩
    have hy' : y ∈ closure (S : Set H) := hy
    obtain ⟨y', hy'S, hdist⟩ := Metric.mem_closure_iff.1 hy' (ε / (3 * (C + 1)))
      (by positivity)
    obtain ⟨i0, hi0⟩ := hspan y' hy'S
    refine ⟨(fun i => xi i y) '' Set.Ici i0, ?_, ?_⟩
    · exact Filter.mem_map.2 (Filter.mem_of_superset (Filter.mem_atTop i0)
        (fun j hj => ⟨j, hj, rfl⟩))
    · rintro _ ⟨j, hj, rfl⟩ _ ⟨k, hk, rfl⟩
      have hb : ∀ l, dist (xi l y) (xi l y') ≤ C * (ε / (3 * (C + 1))) := by
        intro l
        rw [dist_eq_norm, ← map_sub]
        calc ‖xi l (y - y')‖ ≤ ‖xi l‖ * ‖y - y'‖ := (xi l).le_opNorm _
          _ ≤ C * (ε / (3 * (C + 1))) := by
            apply mul_le_mul (hbound l) _ (norm_nonneg _) hC0
            rw [← dist_eq_norm]; exact hdist.le
      have hj' := hi0 j hj
      have hk' := hi0 k hk
      have hCε : C * (ε / (3 * (C + 1))) < ε / 2 := by
        rw [mul_div_assoc', div_lt_div_iff₀ (by positivity) (by norm_num)]
        nlinarith
      calc dist (xi j y) (xi k y) ≤ dist (xi j y) (xi j y') + dist (xi j y') (xi k y) :=
            dist_triangle _ _ _
        _ = dist (xi j y) (xi j y') + dist (xi k y) (xi k y') := by
            rw [hj', ← hk', dist_comm (xi k y')]
        _ < ε / 2 + ε / 2 := add_lt_add_of_le_of_lt ((hb j).trans hCε.le)
            ((hb k).trans_lt hCε)
        _ = ε := by ring
  choose f hf using hconv
  have hfT : Tendsto (fun a x => xi a x) atTop (𝓝 f) := tendsto_pi_nhds.2 hf
  have hbdd : Bornology.IsBounded (Set.range xi) := by
    rw [Metric.isBounded_iff_subset_closedBall 0]
    exact ⟨C, by rintro _ ⟨i, rfl⟩; simpa using hbound i⟩
  set L := ContinuousLinearMap.ofTendstoOfBoundedRange f xi hfT hbdd with hL
  have hLv : ∀ v, L v = f v := fun v => rfl
  refine ⟨L, ?_, ?_, fun v => by rw [hLv]; exact hf v, ?_⟩
  · rw [← SetLike.mem_coe, ← M.centralizer_centralizer, Set.mem_centralizer_iff]
    intro a ha
    rw [Set.mem_centralizer_iff] at ha
    ext v
    simp only [ContinuousLinearMap.mul_apply, hLv]
    have h1 : Tendsto (fun i => a (xi i v)) atTop (𝓝 (a (f v))) :=
      (a.continuous.tendsto _).comp (hf v)
    have h2 : Tendsto (fun i => xi i (a v)) atTop (𝓝 (f (a v))) := hf (a v)
    have heq : (fun i => a (xi i v)) = (fun i => xi i (a v)) := by
      funext i
      have := congrArg (fun T => T v) (ha (xi i) (hxi i))
      simpa using this.symm
    rw [heq] at h1
    exact (tendsto_nhds_unique h2 h1).symm
  · refine ContinuousLinearMap.opNorm_le_bound _ hC0 (fun v => ?_)
    rw [hLv]
    have := (continuous_norm.tendsto _).comp (hf v)
    exact le_of_tendsto' this (fun i => ((xi i).le_opNorm v).trans
      (mul_le_mul_of_nonneg_right (hbound i) (norm_nonneg _)))
  · intro i
    ext z
    simp only [ContinuousLinearMap.mul_apply, hLv]
    have hev : Tendsto (fun j => xi j (proj i z)) atTop (𝓝 (xi i z)) := by
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [Filter.eventually_ge_atTop i] with j hj
      exact (hle' i j hj z).symm
    exact tendsto_nhds_unique hev (hf _)
