-- Prove2me | solution 1 for VectorValuedHolomorphy.exists_continuousOn_extension_of_forall_strongDual_contDiffOn
-- status  : ACCEPTED   (prove)
-- author  : @emmgaml
-- created : 2026-11-22T16:08:28.565139+00:00
-- url     : https://prove2.me/submissions/b24323d3-6d53-4b42-9ffe-faffc1af09a0

import Mathlib

open Filter Topology Metric
open scoped Real

set_option autoImplicit false

namespace Sol_VectorValuedHolomorphy_exists_continuousOn_extension_of_forall_strongDual_contDiffOn

open Bornology Set
open scoped Uniformity

/-- Mackey: a weakly bounded subset of a polynormable space is von Neumann bounded. -/
theorem isVonNBounded_of_dual_bounded {𝕜 E : Type*} [RCLike 𝕜] [AddCommGroup E]
    [Module 𝕜 E] [TopologicalSpace E] [PolynormableSpace 𝕜 E] {s : Set E}
    (h : ∀ f : StrongDual 𝕜 E, ∃ C : ℝ, ∀ x ∈ s, ‖f x‖ ≤ C) : IsVonNBounded 𝕜 s := by
  let hp := PolynormableSpace.withSeminorms 𝕜 E
  refine hp.isVonNBounded_iff_seminorm_bddAbove.mpr fun p ↦ ?_
  rw [bddAbove_def]
  let e : ULift.{0} E ≃ₗ[𝕜] E := ULift.moduleEquiv
  let q := p.val.comp e.toLinearMap
  let : SeminormedAddCommGroup (ULift.{0} E) := q.toSeminormedAddCommGroup
  let : TopologicalSpace (ULift.{0} E) := q.toSeminormedAddCommGroup.toUniformSpace.toTopologicalSpace
  let : NormedSpace 𝕜 (ULift.{0} E) := ⟨fun c x ↦ (map_smul_eq_mul q c x).le⟩
  let : IsTopologicalAddGroup E := hp.topologicalAddGroup
  have he : Continuous e.symm := by
    refine (Metric.continuous_iff' (f := fun y : E ↦ e.symm y)).mpr fun x ε hε ↦ ?_
    have hcont : Continuous (fun y : E ↦ p.val (y - x)) :=
      p.property.comp (continuous_id.sub continuous_const)
    have hsmall := hcont.continuousAt (x := x).eventually_lt continuousAt_const
      (show p.val (x - x) < ε by simpa)
    simp only [dist_eq_norm, ← map_sub]
    exact hsmall
  -- Apply uniform boundedness to the evaluations on the Banach dual for this seminorm.
  let ev (x : s) := NormedSpace.inclusionInDoubleDual 𝕜 (ULift E) (e.symm x)
  obtain ⟨C, hC⟩ := banach_steinhaus (g := ev) fun f ↦ by
    obtain ⟨C, hC⟩ := h (f.comp ⟨e.symm.toLinearMap, he⟩)
    exact ⟨C, fun x ↦ hC x x.property⟩
  refine ⟨C, ?_⟩
  rintro _ ⟨x, hx, rfl⟩
  change ‖e.symm x‖ ≤ C
  rw [← (NormedSpace.inclusionInDoubleDualLi 𝕜).norm_map (e.symm x)]
  exact hC ⟨x, hx⟩

/-- Scalar `C¹` extensions bound the vector difference quotients on any closed ball in the
extension domain, giving uniform continuity on the part where they agree with the scalar
evaluations. -/
theorem uniformContinuousOn_of_scalar_extensions {𝕜 E : Type*} [RCLike 𝕜]
    [AddCommGroup E] [Module 𝕜 E] [UniformSpace E] [IsUniformAddGroup E]
    [PolynormableSpace 𝕜 E]
    {Ω S : Set 𝕜} (hΩ : IsOpen Ω) {x : 𝕜} {r : ℝ} (hball : closedBall x r ⊆ Ω)
    (hS : S ⊆ closedBall x r) {f : 𝕜 → E}
    (hf : ∀ φ : StrongDual 𝕜 E, ∃ g : 𝕜 → 𝕜, ContDiffOn 𝕜 1 g Ω ∧ EqOn g (fun ξ => φ (f ξ)) S) :
    UniformContinuousOn f S := by
  let c (p : 𝕜 × 𝕜) : 𝕜 := p.2 - p.1
  let q (p : 𝕜 × 𝕜) : E := (c p)⁻¹ • (f p.2 - f p.1)
  let D := q '' (S ×ˢ S)
  have hD : IsVonNBounded 𝕜 D := by
    apply isVonNBounded_of_dual_bounded
    intro φ
    obtain ⟨g, hg, heq⟩ := hf φ
    obtain ⟨C, hC⟩ := ((isCompact_closedBall x r).image_of_continuousOn
      ((hg.continuousOn_deriv_of_isOpen hΩ le_rfl).mono hball)).isBounded.exists_norm_le
    refine ⟨max C 0, ?_⟩
    rintro _ ⟨⟨u, v⟩, ⟨hu, hv⟩, rfl⟩
    rcases eq_or_ne v u with rfl | hne
    · simp [q, c]
    have hmean := (convex_closedBall x r).norm_image_sub_le_of_norm_deriv_le
      (f := g) (C := max C 0)
      (fun w hw ↦ (hg.differentiableOn_one w (hball hw)).differentiableAt
        (hΩ.mem_nhds (hball hw)))
      (fun w hw ↦ (hC _ (mem_image_of_mem _ hw)).trans (le_max_left _ _)) (hS hu) (hS hv)
    have hpos : 0 < ‖v - u‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hne)
    change ‖φ ((v - u)⁻¹ • (f v - f u))‖ ≤ max C 0
    rw [map_smul, map_sub φ, smul_eq_mul, norm_mul, norm_inv,
      ← show g v = φ (f v) from heq hv, ← show g u = φ (f u) from heq hu]
    exact (inv_mul_le_iff₀ hpos).mpr (by simpa only [mul_comm] using hmean)
  let l := 𝓤 𝕜 ⊓ 𝓟 (S ×ˢ S)
  have hc : Tendsto c l (𝓝 0) := by
    apply Tendsto.mono_left _ (inf_le_left : l ≤ 𝓤 𝕜)
    rw [_root_.uniformity_eq_comap_nhds_zero]
    exact tendsto_comap
  have hq : ∀ᶠ p in l, q p ∈ D :=
    mem_of_superset (le_principal_iff.mp (inf_le_right : l ≤ 𝓟 (S ×ˢ S)))
      fun p hp ↦ mem_image_of_mem q hp
  rw [UniformContinuousOn, _root_.uniformity_eq_comap_nhds_zero E, tendsto_comap_iff]
  apply (hD.smul_tendsto_zero hq hc).congr
  rintro ⟨u, v⟩
  rcases eq_or_ne v u with rfl | hne
  · simp [q, c]
  · have hne' : c (u, v) ≠ 0 := sub_ne_zero.mpr hne
    exact smul_inv_smul₀ hne' _

end Sol_VectorValuedHolomorphy_exists_continuousOn_extension_of_forall_strongDual_contDiffOn

open Sol_VectorValuedHolomorphy_exists_continuousOn_extension_of_forall_strongDual_contDiffOn in
theorem solution {𝕜 E : Type*} [RCLike 𝕜]
    [AddCommGroup E] [Module 𝕜 E] [UniformSpace E] [IsUniformAddGroup E] [ContinuousSMul 𝕜 E]
    [PolynormableSpace 𝕜 E] [T2Space E] [QuasiCompleteSpace 𝕜 E] {Ω : Set 𝕜} (hΩ : IsOpen Ω)
    {ξ₀ : 𝕜} (hξ₀ : ξ₀ ∈ Ω) {f : 𝕜 → E}
    (hf : ∀ ℓ : StrongDual 𝕜 E, ∃ g : 𝕜 → 𝕜, ContDiffOn 𝕜 1 g Ω ∧
      Set.EqOn g (fun ξ => ℓ (f ξ)) (Ω \ {ξ₀})) :
    ∃ F : 𝕜 → E, ContinuousOn F Ω ∧ Set.EqOn F f (Ω \ {ξ₀}) ∧
      (∀ ℓ : StrongDual 𝕜 E, ContDiffOn 𝕜 1 (fun ξ => ℓ (F ξ)) Ω) ∧
      ∀ F' : 𝕜 → E, ContinuousOn F' Ω → Set.EqOn F' f (Ω \ {ξ₀}) → Set.EqOn F' F Ω := by
  classical
  let S := Ω \ {ξ₀}
  have hS : IsOpen S := hΩ.sdiff isClosed_singleton
  have hlocal {x : 𝕜} {r : ℝ} {T : Set 𝕜} (hball : closedBall x r ⊆ Ω)
      (hT : T ⊆ closedBall x r) (hTS : T ⊆ S) : UniformContinuousOn f T :=
    uniformContinuousOn_of_scalar_extensions hΩ hball hT fun φ ↦
      (hf φ).imp fun _ ⟨hg, heq⟩ ↦ ⟨hg, heq.mono hTS⟩
  have hcont : ContinuousOn f S := by
    intro x hx
    obtain ⟨r, hr, hb⟩ := nhds_basis_closedBall.mem_iff.mp (hS.mem_nhds hx)
    exact ((hlocal (hb.trans Set.sdiff_subset) Set.Subset.rfl hb).continuousOn x
      (mem_closedBall_self hr.le)).mono_of_mem_nhdsWithin
        (mem_nhdsWithin_of_mem_nhds (closedBall_mem_nhds x hr))
  let l := 𝓝[S] ξ₀
  have hl : l.NeBot := by
    change (𝓝[Ω ∩ {ξ₀}ᶜ] ξ₀).NeBot
    rw [nhdsWithin_inter_of_mem (mem_nhdsWithin_of_mem_nhds (hΩ.mem_nhds hξ₀))]
    infer_instance
  obtain ⟨r, hr, hb⟩ := nhds_basis_closedBall.mem_iff.mp (hΩ.mem_nhds hξ₀)
  let T := closedBall ξ₀ r ∩ S
  have hT : T ∈ l :=
    inter_mem (mem_nhdsWithin_of_mem_nhds (closedBall_mem_nhds ξ₀ hr)) self_mem_nhdsWithin
  have hu := hlocal hb (T := T) Set.inter_subset_left Set.inter_subset_right
  have hc : Cauchy (map f l) := by
    refine cauchy_map_iff.mpr ⟨hl, hu.mono_left (le_inf ?_ ?_)⟩
    · exact (Filter.prod_mono nhdsWithin_le_nhds nhdsWithin_le_nhds).trans cauchy_nhds.2
    · rw [← prod_principal_principal]
      exact Filter.prod_mono (le_principal_iff.mpr hT) (le_principal_iff.mpr hT)
  have htb : TotallyBounded (f '' T) := by
    rw [← Set.range_domRestrict, ← Set.image_univ]
    have hsub : TotallyBounded (Set.univ : Set T) :=
      (totallyBounded_preimage isUniformEmbedding_subtype_val.isUniformInducing
        (isCompact_closedBall ξ₀ r).totallyBounded).subset (fun y _ ↦ y.property.1)
    exact hsub.image hu.restrict
  obtain ⟨v, _, hv⟩ := QuasiCompleteSpace.quasiComplete (htb.isVonNBounded 𝕜).closure
    isClosed_closure (map f l) hc (le_principal_iff.mpr (mem_map.mpr
      (mem_of_superset hT fun x hx ↦ subset_closure (Set.mem_image_of_mem f hx))))
  let F := Function.update f ξ₀ v
  have hF : ContinuousOn F Ω := continuousOn_update_iff.mpr ⟨hcont, fun _ ↦ hv⟩
  have heq : Set.EqOn F f S := fun x hx ↦ Function.update_of_ne hx.2 _ _
  have hdense : Ω ⊆ closure S := by
    intro x hx
    rcases eq_or_ne x ξ₀ with rfl | hne
    · exact mem_closure_iff_nhdsWithin_neBot.mpr hl
    · exact subset_closure ⟨hx, hne⟩
  refine ⟨F, hF, heq, ?_, ?_⟩
  · intro φ
    obtain ⟨g, hg, hgEq⟩ := hf φ
    have hscalar : Set.EqOn (fun ξ => φ (F ξ)) g S := fun x hx ↦
      (congrArg φ (heq hx)).trans (hgEq hx).symm
    exact hg.congr (hscalar.of_subset_closure (φ.continuous.comp_continuousOn hF)
      hg.continuousOn Set.sdiff_subset hdense)
  · intro G hG hg
    exact (hg.trans heq.symm).of_subset_closure hG hF Set.sdiff_subset hdense
