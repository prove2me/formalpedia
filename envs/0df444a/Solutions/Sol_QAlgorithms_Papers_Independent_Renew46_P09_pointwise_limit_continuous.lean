-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Renew46.P09.pointwise_limit_continuous
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T05:25:18.262925+00:00
-- url     : https://prove2.me/submissions/4cce10e9-a85f-415d-8d0b-ae1f6a6caa6a

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P09
noncomputable section

open MeasureTheory Filter

open scoped Manifold ContDiff Topology

open QAlgorithms.Papers.Independent.Renew46.P09

theorem solution
    {K V W : Type*} [RCLike K]
    [AddCommGroup V] [Module K V] [Module ℝ V] [IsScalarTower ℝ K V]
    [UniformSpace V] [IsUniformAddGroup V] [TopologicalSpace.MetrizableSpace V] [CompleteSpace V]
    [ContinuousSMul K V] [LocallyConvexSpace ℝ V]
    [AddCommGroup W] [Module K W] [TopologicalSpace W] [TopologicalSpace.MetrizableSpace W]
    [IsTopologicalAddGroup W] [ContinuousSMul K W]
    (seq : ℕ → V →L[K] W) (lam : V → W)
    (hlim : ∀ v : V, Tendsto (fun n => seq n v) atTop (𝓝 (lam v))) :
    Continuous lam := by
  have : (uniformity V).IsCountablyGenerated := IsUniformAddGroup.uniformity_countably_generated
  have : BaireSpace V := inferInstance
  have hadd : ∀ x y, lam (x + y) = lam x + lam y := fun x y =>
    tendsto_nhds_unique (hlim (x + y)) (by simpa using (hlim x).add (hlim y))
  let L : V →+ W := { toFun := lam, map_zero' := by simpa using (hadd 0 0), map_add' := hadd }
  have hL0 : lam 0 = 0 := L.map_zero
  show Continuous L
  refine continuous_of_continuousAt_zero L ?_
  intro U hU
  change U ∈ 𝓝 (lam 0) at hU
  rw [hL0] at hU
  obtain ⟨N1, hN1, hN1U⟩ := exists_nhds_zero_half hU
  obtain ⟨N2, hN2, hN2U⟩ := exists_nhds_zero_half hN1
  have hN2' : N2 ∩ (fun x => -x) ⁻¹' N2 ∈ 𝓝 (0 : W) :=
    inter_mem hN2 (continuous_neg.tendsto' 0 0 neg_zero hN2)
  obtain ⟨N, ⟨hN, hNc⟩, hNsub⟩ := (closed_nhds_basis (0 : W)).mem_iff.1 hN2'
  -- closed sets F m
  let F : ℕ → Set V := fun m => {v | ∀ p, m ≤ p → seq p v - seq m v ∈ N}
  have hFc : ∀ m, IsClosed (F m) := by
    intro m
    simp only [F, Set.ofPred_forall]
    exact isClosed_iInter fun p => isClosed_iInter fun _ =>
      hNc.preimage ((seq p).continuous.sub (seq m).continuous)
  have hFU : ⋃ m, F m = Set.univ := by
    refine Set.eq_univ_of_forall fun v => ?_
    have h2 : Tendsto (fun pq : ℕ × ℕ => seq pq.1 v - seq pq.2 v) (atTop ×ˢ atTop) (𝓝 0) := by
      have := ((hlim v).comp tendsto_fst).sub ((hlim v).comp tendsto_snd)
      simpa using this
    have h3 : ∀ᶠ pq : ℕ × ℕ in atTop ×ˢ atTop, seq pq.1 v - seq pq.2 v ∈ N := h2 hN
    rw [prod_atTop_atTop_eq] at h3
    obtain ⟨m, hm⟩ := Filter.eventually_atTop_prod_self'.1 h3
    exact Set.mem_iUnion.2 ⟨m, fun p hp => hm p hp m le_rfl⟩
  obtain ⟨m, v0, hv0⟩ := nonempty_interior_of_iUnion_of_closed hFc hFU
  have hv0F : v0 ∈ F m := interior_subset hv0
  have hlimN : ∀ x ∈ F m, lam x - seq m x ∈ N := by
    intro x hx
    refine hNc.mem_of_tendsto ((hlim x).sub tendsto_const_nhds) ?_
    exact Filter.eventually_atTop.2 ⟨m, fun p hp => hx p hp⟩
  have hnb1 : (fun w => v0 + w) ⁻¹' F m ∈ 𝓝 (0 : V) :=
    (continuous_const.add continuous_id).tendsto' 0 v0 (by simp)
      (mem_interior_iff_mem_nhds.1 hv0)
  have hnb2 : (seq m) ⁻¹' N ∈ 𝓝 (0 : V) :=
    (seq m).continuous.tendsto' 0 0 (by simp) hN
  rw [Filter.mem_map]
  filter_upwards [hnb1, hnb2] with w hw1 hw2
  have e : L w = ((lam (v0 + w) - seq m (v0 + w)) + -(lam v0 - seq m v0)) + seq m w := by
    change lam w = _
    rw [hadd, map_add]; abel
  show L w ∈ U
  rw [e]
  have a1 := hNsub (hlimN _ hw1)
  have a2 := hNsub (hlimN _ hv0F)
  have a3 := hNsub hw2
  have a4 : seq m w ∈ N1 := by
    simpa using hN2U _ a3.1 0 (mem_of_mem_nhds hN2)
  exact hN1U _ (hN2U _ a1.1 _ a2.2) _ a4
