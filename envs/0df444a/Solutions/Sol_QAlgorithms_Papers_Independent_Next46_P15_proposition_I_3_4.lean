-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Next46.P15.proposition_I_3_4
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-20T18:02:12.276661+00:00
-- url     : https://prove2.me/submissions/5a31244d-d371-4703-86e0-a861f0de271d

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P15
noncomputable section

open QAlgorithms.Papers.Independent.Next46.P15

open Set Filter Topology

open scoped BigOperators

universe u v w z
theorem g63e_lc_of_zero
    {E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
    [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E]
    {F : Type*} [TopologicalSpace F] [AddCommGroup F] [Module ℝ F]
    [IsTopologicalAddGroup F] [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ F] [T2Space F]
    (U : Set E) (hU : IsOpen U) (g : E → F)
    (hg : ∀ x ∈ U, ∀ h : E, HasDirectionalDerivative g x h 0) (x : E) (hx : x ∈ U) :
    ∀ᶠ y in 𝓝 x, g y = g x := by
  obtain ⟨V, ⟨hVn, hVc⟩, hVU⟩ := (LocallyConvexSpace.convex_basis (𝕜 := ℝ) x).mem_iff.1
    (hU.mem_nhds hx)
  filter_upwards [hVn] with y hy
  by_contra hne
  obtain ⟨ℓ, hℓ⟩ := geometric_hahn_banach_point_point hne
  set h := y - x
  have hseg : ∀ t ∈ Icc (0:ℝ) 1, x + t • h ∈ V := by
    intro t ht
    have := hVc (mem_of_mem_nhds hVn) hy (by linarith [ht.2] : (0:ℝ) ≤ 1 - t) ht.1
      (by ring)
    convert this using 1
    simp only [h, smul_sub, sub_smul, one_smul]; abel
  have hder : ∀ t ∈ Icc (0:ℝ) 1, HasDerivAt (fun s : ℝ => ℓ (g (x + s • h))) 0 t := by
    intro t ht
    have h1 := hg _ (hVU (hseg t ht)) h
    unfold HasDirectionalDerivative at h1
    rw [hasDerivAt_iff_tendsto_slope_zero]
    have h2 := ((ℓ.continuous.tendsto 0).comp h1)
    rw [map_zero] at h2
    refine h2.congr' (Eventually.of_forall fun s => ?_)
    simp only [Function.comp, map_smul, map_sub, add_smul, add_assoc]
  have hc := constant_of_has_deriv_right_zero (f := fun s : ℝ => ℓ (g (x + s • h)))
    (a := 0) (b := 1) (fun t ht => (hder t ht).continuousAt.continuousWithinAt)
    (fun t ht => (hder t (Ico_subset_Icc_self ht)).hasDerivWithinAt) 1 ⟨zero_le_one, le_rfl⟩
  simp only [one_smul, zero_smul, add_zero, h, add_sub_cancel] at hc
  rw [hc] at hℓ
  exact lt_irrefl _ hℓ

theorem g63e_dd_eq
    {E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
    {F : Type*} [TopologicalSpace F] [AddCommGroup F] [Module ℝ F] [T2Space F]
    {g : E → F} {x h : E} {y : F} (hy : HasDirectionalDerivative g x h y) :
    directionalDerivative g x h = y :=
  tendsto_nhds_unique (Classical.epsilon_spec (p := HasDirectionalDerivative g x h) ⟨y, hy⟩) hy

theorem g63e_exists_of_smooth
    {E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
    [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
    {F : Type*} [TopologicalSpace F] [AddCommGroup F] [Module ℝ F]
    (U : Set E) (hU : IsOpen U) (g : E → F) (hg : IsMBSmoothOn U g) (x : E) (hx : x ∈ U)
    (h : E) : ∃ y, HasDirectionalDerivative g x h y := by
  obtain ⟨d, h0, -, hlim⟩ := hg
  refine ⟨d 1 x (Fin.snoc (fun i => Fin.elim0 i) h), ?_⟩
  unfold HasDirectionalDerivative
  refine (hlim 0 x hx (fun i => Fin.elim0 i) h).congr' ?_
  have hc : Tendsto (fun t : ℝ => x + t • h) (𝓝[≠] (0:ℝ)) (𝓝 x) := by
    have : Continuous (fun t : ℝ => x + t • h) := by fun_prop
    simpa using (this.tendsto 0).mono_left nhdsWithin_le_nhds
  filter_upwards [hc (hU.mem_nhds hx)] with t ht
  rw [h0 _ ht, h0 _ hx]

theorem solution
    {E : Type u} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
    [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
    [LocallyConvexSpace ℝ E] [T2Space E]
    {F : Type v} [TopologicalSpace F] [AddCommGroup F] [Module ℝ F]
    [IsTopologicalAddGroup F] [ContinuousSMul ℝ F]
    [LocallyConvexSpace ℝ F] [T2Space F]
    {M : Type w} [TopologicalSpace M] [T2Space M] [ChartedSpace E M]
    {N : Type z} [TopologicalSpace N] [T2Space N] [ChartedSpace F N]
    (hM : QAlgorithms.Papers.Independent.Claimed50.P22.BastianiAtlas (E := E) (M := M))
    (hN : QAlgorithms.Papers.Independent.Claimed50.P22.BastianiAtlas (E := F) (M := N))
    (f : M → N) (hf : IsMBSmoothBetween (E := E) (F := F) f) :
    IsLocallyConstant f ↔ HasZeroFiberDifferentials (E := E) (F := F) f := by
  constructor
  · intro hlc c hc d hd p hp hfp h
    apply g63e_dd_eq
    unfold HasDirectionalDerivative
    have hev : ∀ᶠ x in 𝓝 (c p), d (f (c.symm x)) = d (f (c.symm (c p))) := by
      have h1 : Tendsto c.symm (𝓝 (c p)) (𝓝 (c.symm (c p))) :=
        c.continuousAt_symm (c.map_source hp)
      have h2 := h1 ((IsLocallyConstant.iff_eventually_eq f).1 hlc (c.symm (c p)))
      filter_upwards [h2] with x hx
      rw [Set.mem_preimage] at hx
      rw [hx]
    have hcT : Tendsto (fun t : ℝ => c p + t • h) (𝓝[≠] (0:ℝ)) (𝓝 (c p)) := by
      have : Continuous (fun t : ℝ => c p + t • h) := by fun_prop
      simpa using (this.tendsto 0).mono_left nhdsWithin_le_nhds
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [hcT hev] with t ht
    rw [Set.mem_preimage] at ht
    rw [ht, sub_self, smul_zero]
  · intro hz
    rw [IsLocallyConstant.iff_eventually_eq]
    intro p
    set c := chartAt E p
    set d := chartAt F (f p)
    have hc : c ∈ atlas E M := chart_mem_atlas E p
    have hd : d ∈ atlas F N := chart_mem_atlas F (f p)
    set W := c.target ∩ (fun x => f (c.symm x)) ⁻¹' d.source
    have hWo : IsOpen W := by
      apply ContinuousOn.isOpen_inter_preimage _ c.open_target d.open_source
      exact hf.1.comp_continuousOn c.continuousOn_symm
    have hpW : c p ∈ W := ⟨c.map_source (mem_chart_source E p), by
      simp only [Set.mem_preimage, c.left_inv (mem_chart_source E p)]
      exact mem_chart_source F (f p)⟩
    have hzero : ∀ x ∈ W, ∀ h : E,
        HasDirectionalDerivative (fun x => d (f (c.symm x))) x h 0 := by
      intro x hx h
      obtain ⟨y, hy⟩ := g63e_exists_of_smooth W hWo _ (hf.2 c hc d hd) x hx h
      have hq := hz c hc d hd (c.symm x) (c.map_target hx.1) hx.2 h
      rw [c.right_inv hx.1] at hq
      rw [← hq, g63e_dd_eq hy]; exact hy
    have hev := g63e_lc_of_zero W hWo _ hzero (c p) hpW
    have hcp : Tendsto c (𝓝 p) (𝓝 (c p)) := c.continuousAt (mem_chart_source E p)
    have hsrc : ∀ᶠ q in 𝓝 p, q ∈ c.source := c.open_source.mem_nhds (mem_chart_source E p)
    have hfs : ∀ᶠ q in 𝓝 p, f q ∈ d.source :=
      hf.1.continuousAt.preimage_mem_nhds (d.open_source.mem_nhds (mem_chart_source F (f p)))
    filter_upwards [hcp hev, hsrc, hfs] with q hq hqs hqf
    have hq' : d (f (c.symm (c q))) = d (f (c.symm (c p)))  := hq
    rw [c.left_inv hqs, c.left_inv (mem_chart_source E p)] at hq'
    exact d.injOn hqf (mem_chart_source F (f p)) hq'

end
