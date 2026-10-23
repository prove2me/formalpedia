-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Next46.P15.remark_I_5_4
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T11:30:14.77769+00:00
-- url     : https://prove2.me/submissions/1b47ce2f-2d32-4ed0-bde4-7259b1e14204

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P15

namespace X6P15b

open Filter Topology Set Pointwise

universe u

variable {E : Type u} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
    [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]

/-- If a 0-neighbourhood `U` is controlled by the sup over a compact set `K`, then `E` is
spanned by finitely many points of `K` modulo functionals; i.e. every functional vanishing on a
suitable finite subset of `K` vanishes. -/
lemma vanish_of_bound (K U : Set E) (hK : IsCompact K) (hU : U ∈ 𝓝 (0 : E)) (ε : ℝ) (hε : 0 < ε)
    (hb : ∀ α : E →L[ℝ] ℝ, ∀ M : ℝ, 0 ≤ M → (∀ y ∈ K, |α y| ≤ M) → ∀ x ∈ U, |α x| ≤ M / ε) :
    ∃ t : Finset E, ∀ α : E →L[ℝ] ℝ, (∀ k ∈ t, α k = 0) → α = 0 := by
  set δ : ℝ := ε / 2 with hδ
  have hδ0 : δ ≠ 0 := by positivity
  have hδU : δ • U ∈ 𝓝 (0 : E) := (set_smul_mem_nhds_zero_iff hδ0).2 hU
  obtain ⟨t, -, ht⟩ := hK.elim_nhds_subcover (fun k => (fun y => y - k) ⁻¹' (δ • U)) (by
    intro k _
    have hc : Continuous (fun y : E => y - k) := continuous_id.sub continuous_const
    exact hc.continuousAt.preimage_mem_nhds (by simpa using hδU))
  refine ⟨t, fun α hα => ?_⟩
  -- the bound on K halves
  have half : ∀ M : ℝ, 0 ≤ M → (∀ y ∈ K, |α y| ≤ M) → ∀ y ∈ K, |α y| ≤ M / 2 := by
    intro M hM0 hM y hy
    have := ht hy
    simp only [mem_iUnion, mem_preimage] at this
    obtain ⟨k, hk, hyk⟩ := this
    obtain ⟨u, hu, hu'⟩ := Set.mem_smul_set.1 hyk
    have hy' : y = k + δ • u := by rw [hu']; abel
    have h1 := hb α M hM0 hM u hu
    rw [hy', map_add, map_smul, hα k hk, zero_add, smul_eq_mul, abs_mul, abs_of_pos (by positivity)]
    calc δ * |α u| ≤ δ * (M / ε) := by gcongr
      _ = M / 2 := by rw [hδ]; field_simp
  -- initial bound on K
  obtain ⟨M0, hM0⟩ := hK.exists_bound_of_continuousOn (f := fun y => α y)
    (α.continuous.continuousOn)
  have hall : ∀ n : ℕ, ∀ y ∈ K, |α y| ≤ |M0| / 2 ^ n := by
    intro n; induction n with
    | zero => intro y hy; simpa [Real.norm_eq_abs] using (hM0 y hy).trans (le_abs_self M0)
    | succ n ih =>
      intro y hy; have := half _ (by positivity) ih y hy; rw [pow_succ, ← div_div]; exact this
  have hK0 : ∀ y ∈ K, |α y| ≤ 0 := by
    intro y hy
    have ht : Tendsto (fun n : ℕ => |M0| / 2 ^ n) atTop (𝓝 0) := by
      have := (tendsto_pow_atTop_nhds_zero_of_lt_one (r := (1/2 : ℝ)) (by norm_num)
        (by norm_num)).const_mul |M0|
      simpa [div_eq_mul_inv, inv_pow] using this
    exact ge_of_tendsto ht (Eventually.of_forall fun n => hall n y hy)
  have hU0 : ∀ x ∈ U, α x = 0 := by
    intro x hx; have := hb α 0 le_rfl hK0 x hx; rw [zero_div] at this
    exact abs_nonpos_iff.1 this
  ext x
  have hc : Tendsto (fun s : ℝ => s • x) (𝓝 0) (𝓝 0) := by
    exact Continuous.tendsto' (f := fun s : ℝ => s • x) (by fun_prop) 0 0 (by simp)
  have hev : ∀ᶠ s : ℝ in 𝓝[≠] 0, s • x ∈ U := (hc.mono_left nhdsWithin_le_nhds) hU
  obtain ⟨s, hs, hs0⟩ := (hev.and self_mem_nhdsWithin).exists
  have := hU0 _ hs
  rw [map_smul, smul_eq_mul] at this
  exact (mul_eq_zero.1 this).resolve_left hs0

variable [LocallyConvexSpace ℝ E] [T2Space E]

lemma finiteDimensional_of_vanish (t : Finset E)
    (h : ∀ α : E →L[ℝ] ℝ, (∀ k ∈ t, α k = 0) → α = 0) : FiniteDimensional ℝ E := by
  set F : Submodule ℝ E := Submodule.span ℝ (t : Set E)
  have hF : F = ⊤ := by
    by_contra hne
    obtain ⟨x, hx⟩ : ∃ x, x ∉ F := by
      by_contra h'; push Not at h'; exact hne (eq_top_iff.2 fun x _ => h' x)
    have hcl : IsClosed (F : Set E) := Submodule.closed_of_finiteDimensional F
    obtain ⟨f, u, hfF, hux⟩ := geometric_hahn_banach_closed_point (F.convex) hcl hx
    have hf0 : ∀ a ∈ F, f a = 0 := by
      intro a ha
      by_contra hfa
      have hs : ((|u| + 1) / f a) • a ∈ F := F.smul_mem _ ha
      have := hfF _ hs
      rw [map_smul, smul_eq_mul, div_mul_cancel₀ _ hfa] at this
      linarith [le_abs_self u]
    have := h f (fun k hk => hf0 k (Submodule.subset_span hk))
    have h0 := hfF 0 F.zero_mem
    rw [this] at hux h0
    simp at hux h0
    linarith
  exact Module.finite_def.2 ⟨t, hF⟩

end X6P15b

universe u

open QAlgorithms.Papers.Independent.Next46.P15

open Set Filter Topology

theorem solution
    {E : Type u} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
    [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
    [LocallyConvexSpace ℝ E] [T2Space E]
    (hInfinite : ¬ FiniteDimensional ℝ E) :
    letI : TopologicalSpace (E →L[ℝ] ℝ) := compactDualTopology E
    ¬ Continuous (fun p : E × (ℝ × (E →L[ℝ] ℝ)) =>
      (p.2.1 + p.2.2 p.1, p.2.2)) := by
  letI τ : TopologicalSpace (E →L[ℝ] ℝ) := compactDualTopology E
  intro hcont
  apply hInfinite
  -- evaluation is continuous
  have hg : Continuous (fun p : E × (E →L[ℝ] ℝ) => p.2 p.1) := by
    have h1 : Continuous (fun p : E × (E →L[ℝ] ℝ) => ((p.1, ((0 : ℝ), p.2)) :
        E × (ℝ × (E →L[ℝ] ℝ)))) :=
      continuous_fst.prodMk (continuous_const.prodMk continuous_snd)
    exact (continuous_fst.comp (hcont.comp h1)).congr fun p => by simp
  have hpre : (fun p : E × (E →L[ℝ] ℝ) => p.2 p.1) ⁻¹' Ioo (-1) 1 ∈ 𝓝 ((0 : E), (0 : E →L[ℝ] ℝ)) :=
    hg.continuousAt.preimage_mem_nhds (Ioo_mem_nhds (by simp) (by simp))
  rw [nhds_prod_eq, mem_prod_iff] at hpre
  obtain ⟨U, hU, W, hW, hUW⟩ := hpre
  -- unpack the compact-open neighbourhood
  have hW' : W ∈ comap (fun ell : E →L[ℝ] ℝ => (⟨fun x => ell x, ell.continuous⟩ : C(E, ℝ)))
      (𝓝 (⟨fun x => (0 : E →L[ℝ] ℝ) x, (0 : E →L[ℝ] ℝ).continuous⟩ : C(E, ℝ))) := by
    rw [← nhds_induced]; exact hW
  obtain ⟨W', hW'1, hW'2⟩ := hW'
  rw [nhds_eq_comap_uniformity, mem_comap] at hW'1
  obtain ⟨S, hS, hSW⟩ := hW'1
  rw [ContinuousMap.hasBasis_compactConvergenceUniformity.mem_iff] at hS
  obtain ⟨⟨K, V⟩, ⟨hK, hV⟩, hKV⟩ := hS
  obtain ⟨ε, hε, hεV⟩ := Metric.mem_uniformity_dist.1 hV
  have hsmall : ∀ α : E →L[ℝ] ℝ, (∀ y ∈ K, |α y| < ε) → ∀ x ∈ U, |α x| < 1 := by
    intro α hα x hx
    have hαW : α ∈ W := by
      apply hW'2; apply hSW; apply hKV
      intro y hy
      apply hεV
      simpa [Real.dist_eq, abs_sub_comm] using hα y hy
    have := hUW (mk_mem_prod hx hαW)
    simp only [mem_preimage, mem_Ioo] at this
    exact abs_lt.2 this
  have hb : ∀ α : E →L[ℝ] ℝ, ∀ M : ℝ, 0 ≤ M → (∀ y ∈ K, |α y| ≤ M) → ∀ x ∈ U, |α x| ≤ M / ε := by
    intro α M hM0 hM x hx
    rw [le_div_iff₀ hε]
    apply le_of_forall_gt
    intro r hr
    have hr0 : 0 < r := lt_of_le_of_lt hM0 hr
    have hc0 : 0 < ε / r := by positivity
    have := hsmall ((ε / r) • α) (by
      intro y hy
      rw [ContinuousLinearMap.smul_apply, smul_eq_mul, abs_mul, abs_of_pos hc0]
      calc ε / r * |α y| ≤ ε / r * M := by gcongr; exact hM y hy
        _ < ε / r * r := by gcongr
        _ = ε := by field_simp) x hx
    rw [ContinuousLinearMap.smul_apply, smul_eq_mul, abs_mul, abs_of_pos hc0] at this
    rw [div_mul_eq_mul_div, div_lt_one hr0] at this
    linarith
  obtain ⟨t, ht⟩ := X6P15b.vanish_of_bound K U hK hU ε hε hb
  exact X6P15b.finiteDimensional_of_vanish t ht

