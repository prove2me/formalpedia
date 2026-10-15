-- Prove2me | solution 1 for Plasticity.Faces.preimage_face_of_boundary_compact
-- status  : ACCEPTED   (prove)
-- author  : @scanstone
-- created : 2026-10-15T00:43:38.440916+00:00
-- url     : https://prove2.me/submissions/17b4c030-96aa-45f6-8cd5-d3fdb6e1bde8

import Theorems.Thm_Plasticity_BallMap_map_zero_of_surjOn
import Theorems.Thm_Plasticity_BallMap_norm_map_le
import Theorems.Thm_Plasticity_BallMap_mem_sphere_of_map_mem_sphere
import Theorems.Thm_Plasticity_BallMap_norm_map_eq_of_mapsTo_sphere
import Theorems.Thm_Plasticity_BallMap_map_neg_of_map_mem_extremePoints
import Theorems.Thm_Plasticity_BallMap_mem_extremePoints_of_map_mem_extremePoints
import Theorems.Thm_Plasticity_BallMap_map_smul_of_map_mem_extremePoints
import Theorems.Thm_Plasticity_Faces_isCompact_and_eq_closedBall_inter_affineSpan
import Theorems.Thm_Plasticity_Topology_mem_intrinsicInterior_iff_ball
import Theorems.Thm_Plasticity_Topology_exists_closedBall_model_of_convex_compact
import Theorems.Thm_Plasticity_Topology_mapsTo_intrinsicInterior_of_injOn
import Theorems.Thm_Plasticity_Topology_finrank_vectorSpan_le_of_injOn
import Theorems.Thm_Plasticity_Faces_reflected_preimage_eq_cone
import Theorems.Thm_Plasticity_Faces_matchesFace_singleton
import Definitions.Def_Plasticity_Faces
import Mathlib.Topology.EMetricSpace.Lipschitz
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Module.RCLike.Real
import Mathlib.Analysis.Convex.Segment
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Topology.Order.Monotone
import Mathlib.Tactic.Module

namespace Sol_Plasticity_Faces_preimage_face_of_boundary_compact

/-- The basic facts of the cards `Plasticity.BallMap.*` (claim U01), bundled for this file. -/
theorem ballMap_facts {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] (F : X → Y)
    (hbij : Set.BijOn F (Metric.closedBall (0 : X) 1) (Metric.closedBall (0 : Y) 1))
    (hlip : LipschitzOnWith 1 F (Metric.closedBall (0 : X) 1)) :
    F 0 = 0 ∧
    (∀ x ∈ Metric.closedBall (0 : X) 1, ‖F x‖ ≤ ‖x‖) ∧
    (∀ x ∈ Metric.closedBall (0 : X) 1, F x ∈ Metric.sphere (0 : Y) 1 → x ∈ Metric.sphere (0 : X) 1) ∧
    (∀ x ∈ Metric.closedBall (0 : X) 1, F x ∈ (Metric.closedBall (0 : Y) 1).extremePoints ℝ →
      x ∈ (Metric.closedBall (0 : X) 1).extremePoints ℝ ∧ F (-x) = -F x ∧
        ∀ t ∈ Set.Icc (-1 : ℝ) 1, F (t • x) = t • F x) ∧
    (Set.MapsTo F (Metric.sphere (0 : X) 1) (Metric.sphere (0 : Y) 1) →
      ∀ x ∈ Metric.closedBall (0 : X) 1, ‖F x‖ = ‖x‖) :=
  ⟨Plasticity.BallMap.map_zero_of_surjOn F hbij.surjOn hlip,
    fun x hx => Plasticity.BallMap.norm_map_le F hbij.surjOn hlip x hx,
    fun x hx hs => Plasticity.BallMap.mem_sphere_of_map_mem_sphere F hbij.surjOn hlip x hx hs,
    fun x hx he => ⟨Plasticity.BallMap.mem_extremePoints_of_map_mem_extremePoints F hbij hlip x hx he,
      Plasticity.BallMap.map_neg_of_map_mem_extremePoints F hbij hlip x hx he,
      fun t ht => Plasticity.BallMap.map_smul_of_map_mem_extremePoints F hbij hlip x hx he t ht⟩,
    fun hs x hx => Plasticity.BallMap.norm_map_eq_of_mapsTo_sphere F hbij.surjOn hlip hs x hx⟩

end Sol_Plasticity_Faces_preimage_face_of_boundary_compact


namespace Sol_Plasticity_Faces_preimage_face_of_boundary_compact

open Set Metric Topology Filter

/-- A left inverse of a continuous map on a compact set is continuous on the image. -/
lemma contOn_leftInv {α β : Type*} [TopologicalSpace α] [TopologicalSpace β] [T2Space β]
    {f : α → β} {g : β → α} {K : Set α} (hK : IsCompact K) (hf : ContinuousOn f K)
    (hgf : ∀ x ∈ K, g (f x) = x) : ContinuousOn g (f '' K) := by
  rw [continuousOn_iff_isClosed]
  intro t ht
  refine ⟨f '' (K ∩ t),
    ((hK.inter_right ht).image_of_continuousOn (hf.mono inter_subset_left)).isClosed, ?_⟩
  ext y
  constructor
  · rintro ⟨hy1, ⟨x, hx, rfl⟩⟩
    refine ⟨⟨x, ⟨hx, ?_⟩, rfl⟩, ⟨x, hx, rfl⟩⟩
    have h1 : g (f x) ∈ t := hy1
    rwa [hgf x hx] at h1
  · rintro ⟨⟨x, ⟨hxK, hxt⟩, rfl⟩, hy2⟩
    refine ⟨?_, hy2⟩
    show g (f x) ∈ t
    rw [hgf x hxK]
    exact hxt

lemma frontier_eq_sdiff {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {C : Set E}
    (hC : IsClosed C) : intrinsicFrontier ℝ C = C \ intrinsicInterior ℝ C := by
  have hcl : intrinsicClosure ℝ C = C :=
    Subset.antisymm (intrinsicClosure_subset_closure.trans hC.closure_subset)
      subset_intrinsicClosure
  rw [← intrinsicClosure_sdiff_intrinsicInterior, hcl]

variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]

omit [NormedSpace ℝ X] in
/-- Step 1 of Lemma 2 (two balls). -/
lemma two_balls (F : X → Y) (hlip : LipschitzOnWith 1 F (closedBall (0 : X) 1)) {C : Set Y}
    (hconv : Convex ℝ C) (hext : IsExtreme ℝ (closedBall (0 : Y) 1) C) {u v w : X}
    (hu : u ∈ closedBall (0 : X) 1) (hFu : F u ∈ C) (hv : v ∈ closedBall (0 : X) 1)
    (hFv : -F (-v) ∈ C) (hw : w ∈ closedBall (0 : X) 1) (huw : ‖u - w‖ ≤ 1)
    (hvw : ‖v + w‖ ≤ 1) : F w ∈ vectorSpan ℝ C := by
  have hnv : -v ∈ closedBall (0 : X) 1 := by simpa using hv
  have hp : F u - F w ∈ closedBall (0 : Y) 1 := by
    rw [mem_closedBall_zero_iff, ← dist_eq_norm]
    have h1 := hlip.dist_le_mul u hu w hw
    simp only [NNReal.coe_one, one_mul] at h1
    exact h1.trans (by rw [dist_eq_norm]; exact huw)
  have hq : F w - F (-v) ∈ closedBall (0 : Y) 1 := by
    rw [mem_closedBall_zero_iff, ← dist_eq_norm]
    have h1 := hlip.dist_le_mul w hw (-v) hnv
    simp only [NNReal.coe_one, one_mul] at h1
    exact h1.trans (by rw [dist_eq_norm, sub_neg_eq_add, add_comm]; exact hvw)
  have hmid : (1 / 2 : ℝ) • (F u - F w) + (1 / 2 : ℝ) • (F w - F (-v)) ∈ C := by
    have h1 := hconv hFu hFv (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num)
    convert h1 using 1
    simp only [smul_sub, smul_neg]
    abel
  have hseg : (1 / 2 : ℝ) • (F u - F w) + (1 / 2 : ℝ) • (F w - F (-v)) ∈
      openSegment ℝ (F u - F w) (F w - F (-v)) :=
    ⟨1 / 2, 1 / 2, by norm_num, by norm_num, by norm_num, rfl⟩
  have hpC := hext.left_mem_of_mem_openSegment hp hq hmid hseg
  have h2 := vsub_mem_vectorSpan ℝ hFu hpC
  simpa using h2

end Sol_Plasticity_Faces_preimage_face_of_boundary_compact

open Set Metric Topology Filter Sol_Plasticity_Faces_preimage_face_of_boundary_compact Plasticity in
open scoped Pointwise in
theorem solution {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (F : X → Y)
    (hbij : Set.BijOn F (Metric.closedBall (0 : X) 1) (Metric.closedBall (0 : Y) 1))
    (hlip : LipschitzOnWith 1 F (Metric.closedBall (0 : X) 1))
    (C : Set Y) (hC : IsSphereFace C) (hfin : FiniteDimensional ℝ (vectorSpan ℝ C))
    (hAc : IsCompact (Metric.closedBall (0 : X) 1 ∩ F ⁻¹' intrinsicFrontier ℝ C))
    (hAe : IsExtreme ℝ (Metric.closedBall (0 : X) 1)
      (Metric.closedBall (0 : X) 1 ∩ F ⁻¹' intrinsicFrontier ℝ C))
    (hAs : ∀ x ∈ Metric.closedBall (0 : X) 1,
      F x ∈ intrinsicFrontier ℝ C ↔ -F (-x) ∈ intrinsicFrontier ℝ C) :
    IsSphereFace (Metric.closedBall (0 : X) 1 ∩ F ⁻¹' C) ∧
    IsCompact (Metric.closedBall (0 : X) 1 ∩ F ⁻¹' C) ∧
    FiniteDimensional ℝ (vectorSpan ℝ (Metric.closedBall (0 : X) 1 ∩ F ⁻¹' C)) ∧
    Module.finrank ℝ (vectorSpan ℝ (Metric.closedBall (0 : X) 1 ∩ F ⁻¹' C)) =
      Module.finrank ℝ (vectorSpan ℝ C) ∧
    Metric.closedBall (0 : X) 1 ∩ F ⁻¹' (-C) = -(Metric.closedBall (0 : X) 1 ∩ F ⁻¹' C) ∧
    Metric.closedBall (0 : X) 1 ∩ F ⁻¹' (intrinsicFrontier ℝ C) =
      intrinsicFrontier ℝ (Metric.closedBall (0 : X) 1 ∩ F ⁻¹' C) := by
  rcases Nat.eq_zero_or_pos (Module.finrank ℝ (vectorSpan ℝ C)) with h0 | hn
  · -- dimension 0: `C = {e}` for an extreme point `e` of the unit ball
    have hss : C.Subsingleton :=
      (vectorSpan_eq_bot_iff_subsingleton ℝ).mp (Submodule.finrank_eq_zero.mp h0)
    obtain ⟨e, he⟩ := hC.1
    obtain rfl := hss.eq_singleton_of_mem he
    obtain ⟨h1, h2, h3, h4, h5, h6, -⟩ := Plasticity.Faces.matchesFace_singleton F hbij hlip e hC
    exact ⟨h1, h2, h3, h4, h5, h6⟩
  replace hn : 1 ≤ Module.finrank ℝ (vectorSpan ℝ C) := hn
  have hC' := hC
  obtain ⟨hCne, hCconv, hCsph, hCext⟩ := hC
  have hfin' := hfin
  obtain ⟨hCcpt, -⟩ := Plasticity.Faces.isCompact_and_eq_closedBall_inter_affineSpan C hC' hfin
  have hCcl : IsClosed C := hCcpt.isClosed
  have hbdC : intrinsicFrontier ℝ C ⊆ C := intrinsicFrontier_subset hCcl
  have hCB : C ⊆ closedBall (0 : Y) 1 := hCext.subset
  obtain ⟨hF0, hFnorm, hFsph, -, -⟩ := Sol_Plasticity_Faces_preimage_face_of_boundary_compact.ballMap_facts F hbij hlip
  have hFcont : ContinuousOn F (closedBall (0 : X) 1) := hlip.continuousOn
  set A := closedBall (0 : X) 1 ∩ F ⁻¹' intrinsicFrontier ℝ C with hA
  set D := closedBall (0 : X) 1 ∩ F ⁻¹' C with hD
  have hAD : A ⊆ D := fun x hx => ⟨hx.1, hbdC hx.2⟩
  have hFinjD : InjOn F D := hbij.injOn.mono inter_subset_left
  have hFcontD : ContinuousOn F D := hFcont.mono inter_subset_left
  -- the reflected map
  set Ft : X → Y := fun x => -F (-x) with hFt
  have hnegB : ∀ x ∈ closedBall (0 : X) 1, -x ∈ closedBall (0 : X) 1 :=
    fun x hx => by simpa using hx
  have hbijt : BijOn Ft (closedBall (0 : X) 1) (closedBall (0 : Y) 1) := by
    refine ⟨fun x hx => by simpa [Ft] using hbij.mapsTo (hnegB x hx), ?_, ?_⟩
    · intro x hx y hy h
      exact neg_injective (hbij.injOn (hnegB x hx) (hnegB y hy) (neg_injective h))
    · intro y hy
      obtain ⟨x, hx, hxy⟩ := hbij.surjOn (show -y ∈ closedBall (0 : Y) 1 by simpa using hy)
      exact ⟨-x, hnegB x hx, by simp [Ft, hxy]⟩
  have hlipt : LipschitzOnWith 1 Ft (closedBall (0 : X) 1) := by
    refine LipschitzOnWith.of_dist_le_mul fun x hx y hy => ?_
    have h1 := hlip.dist_le_mul (-x) (hnegB x hx) (-y) (hnegB y hy)
    simpa [Ft, dist_neg_neg] using h1
  have hAt : closedBall (0 : X) 1 ∩ Ft ⁻¹' intrinsicFrontier ℝ C = A := by
    ext x
    constructor
    · rintro ⟨hx, h⟩
      exact ⟨hx, (hAs x hx).mpr h⟩
    · rintro ⟨hx, h⟩
      exact ⟨hx, (hAs x hx).mp h⟩
  have hAst : ∀ x ∈ closedBall (0 : X) 1,
      Ft x ∈ intrinsicFrontier ℝ C ↔ -Ft (-x) ∈ intrinsicFrontier ℝ C := by
    intro x hx
    simp only [Ft, neg_neg]
    exact (hAs x hx).symm
  -- Steps 1–4 for `F` and for `Ft`
  obtain ⟨-, hconeF⟩ := Plasticity.Faces.reflected_preimage_eq_cone F hbij hlip C hC' hn hAc hAe hAs
  obtain ⟨hDc', hconeFt⟩ := Plasticity.Faces.reflected_preimage_eq_cone Ft hbijt hlipt C hC' hn
    (hAt ▸ hAc) (hAt ▸ hAe) hAst
  have hDset : {x | x ∈ closedBall (0 : X) 1 ∧ -Ft (-x) ∈ C} = D := by
    ext x
    simp [Ft, D]
  have hDc : IsCompact D := hDset ▸ hDc'
  have hDcl : IsClosed D := hDc.isClosed
  have hconeFt' : ∀ u ∈ closedBall (0 : X) 1, Ft u ∈ C → Ft u ∉ intrinsicFrontier ℝ C →
      ∀ x, x ∈ D ↔ ∃ a ∈ A, x ∈ segment ℝ u a := by
    intro u hu h1 h2 x
    have h := hconeFt u hu h1 h2 x
    rw [hAt] at h
    rw [← h]
    simp [Ft, D]
  set D' := {x | x ∈ closedBall (0 : X) 1 ∧ -F (-x) ∈ C} with hD'
  obtain ⟨c₀, hc₀⟩ := hCne
  have hDD' : D = D' := by
    apply Subset.antisymm
    · intro x hx
      by_cases hxA : x ∈ A
      · exact ⟨hx.1, hbdC ((hAs x hx.1).mp hxA.2)⟩
      · have hFxA : F x ∉ intrinsicFrontier ℝ C := fun h => hxA ⟨hx.1, h⟩
        obtain ⟨y, hyB, hy⟩ := hbijt.surjOn (hCB hc₀)
        obtain ⟨a, haA, -⟩ := (hconeF x hx.1 hx.2 hFxA y).mp ⟨hyB, by
          have : Ft y ∈ C := hy ▸ hc₀
          exact this⟩
        exact (hconeF x hx.1 hx.2 hFxA x).mpr ⟨a, haA, left_mem_segment ℝ x a⟩
    · intro x hx
      by_cases hxA : x ∈ A
      · exact hAD hxA
      · have hFtxA : Ft x ∉ intrinsicFrontier ℝ C := fun h => hxA ⟨hx.1, (hAs x hx.1).mpr h⟩
        obtain ⟨y, hyB, hy⟩ := hbij.surjOn (hCB hc₀)
        obtain ⟨a, haA, -⟩ := (hconeFt' x hx.1 hx.2 hFtxA y).mp ⟨hyB, by
          show F y ∈ C
          rw [hy]
          exact hc₀⟩
        exact (hconeFt' x hx.1 hx.2 hFtxA x).mpr ⟨a, haA, left_mem_segment ℝ x a⟩
  have hrep : ∀ u ∈ D, u ∉ A → ∀ x, x ∈ D ↔ ∃ a ∈ A, x ∈ segment ℝ u a := by
    intro u hu huA x
    rw [hDD']
    exact hconeF u hu.1 hu.2 (fun h => huA ⟨hu.1, h⟩) x
  -- the inverse `G` on `C`
  set G : Y → X := Function.invFunOn F (closedBall (0 : X) 1) with hG
  have hG1 : ∀ y ∈ closedBall (0 : Y) 1, G y ∈ closedBall (0 : X) 1 ∧ F (G y) = y :=
    fun y hy => ⟨Function.invFunOn_mem (hbij.surjOn hy), Function.invFunOn_eq (hbij.surjOn hy)⟩
  have hG2 : ∀ x ∈ closedBall (0 : X) 1, G (F x) = x := fun x hx =>
    hbij.injOn (hG1 _ (hbij.mapsTo hx)).1 hx (hG1 _ (hbij.mapsTo hx)).2
  have hGD : MapsTo G C D := by
    intro y hy
    obtain ⟨h1, h2⟩ := hG1 y (hCB hy)
    exact ⟨h1, by rw [mem_preimage, h2]; exact hy⟩
  have hFD : F '' D = C := by
    apply Subset.antisymm
    · rintro _ ⟨x, hx, rfl⟩
      exact hx.2
    · intro y hy
      exact ⟨G y, hGD hy, (hG1 y (hCB hy)).2⟩
  have hGc : ContinuousOn G C :=
    hFD ▸ contOn_leftInv hDc hFcontD (fun x hx => hG2 x hx.1)
  have hGinj : InjOn G C := by
    intro y₁ h₁ y₂ h₂ h
    rw [← (hG1 y₁ (hCB h₁)).2, ← (hG1 y₂ (hCB h₂)).2, h]
  -- an apex `u₀ ∈ D \ A`
  obtain ⟨φ, ψ, -, -, hφ, -⟩ := Plasticity.Topology.exists_closedBall_model_of_convex_compact C hCcpt hCconv ⟨c₀, hc₀⟩ hfin
  have hφ0 := hφ 0 (by simp)
  set u₀ := G (φ 0) with hu₀
  have hu₀D : u₀ ∈ D := hGD hφ0.1
  have hFu₀ : F u₀ = φ 0 := (hG1 _ (hCB hφ0.1)).2
  have hu₀A : u₀ ∉ A := by
    intro h
    have h1 := h.2
    rw [mem_preimage, hFu₀] at h1
    have h2 := hφ0.2.2.mp h1
    simp at h2
  -- segments from points of `D \ A`
  have hseg_u : ∀ u ∈ D, u ∉ A → ∀ v ∈ D, segment ℝ u v ⊆ D := by
    intro u hu huA v hv x hx
    obtain ⟨a, haA, hva⟩ := (hrep u hu huA v).mp hv
    have hxa : x ∈ segment ℝ u a :=
      (convex_segment u a).segment_subset (left_mem_segment ℝ u a) hva hx
    exact (hrep u hu huA x).mpr ⟨a, haA, hxa⟩
  -- Step 5: convexity
  have hconvD : Convex ℝ D := by
    intro p hp q hq a b ha hb hab
    by_cases hpA : p ∈ A
    · have hlim : Tendsto (fun ε : ℝ => a • (p + ε • (u₀ - p)) + b • q) (𝓝[>] 0)
          (𝓝 (a • p + b • q)) := by
        have hc : Continuous (fun ε : ℝ => a • (p + ε • (u₀ - p)) + b • q) := by fun_prop
        have h := hc.tendsto 0
        simp only [zero_smul, add_zero] at h
        exact h.mono_left nhdsWithin_le_nhds
      apply hDcl.mem_of_tendsto hlim
      filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1)] with ε hε
      have hpεD : p + ε • (u₀ - p) ∈ D := by
        apply hseg_u u₀ hu₀D hu₀A p hp
        rw [segment_symm, segment_eq_image']
        exact ⟨ε, ⟨hε.1.le, hε.2.le⟩, rfl⟩
      have hpεA : p + ε • (u₀ - p) ∉ A := by
        intro h
        apply hu₀A
        exact hAe.right_mem_of_mem_openSegment hp.1 hu₀D.1 h
          (by rw [openSegment_eq_image']; exact ⟨ε, hε, rfl⟩)
      exact hseg_u _ hpεD hpεA q hq ⟨a, b, ha, hb, hab, rfl⟩
    · exact hseg_u p hp hpA q hq ⟨a, b, ha, hb, hab, rfl⟩
  -- dimension
  obtain ⟨hDfin, hDle⟩ := Plasticity.Topology.finrank_vectorSpan_le_of_injOn D hconvD F hFcontD hFinjD
    (vectorSpan ℝ C) hfin (F u₀) (fun x hx => vsub_mem_vectorSpan ℝ hx.2 hu₀D.2)
  obtain ⟨-, hCle⟩ := Plasticity.Topology.finrank_vectorSpan_le_of_injOn C hCconv G hGc hGinj (vectorSpan ℝ D) hDfin u₀
    (fun y hy => vsub_mem_vectorSpan ℝ (hGD hy) hu₀D)
  have hdim : Module.finrank ℝ (vectorSpan ℝ D) = Module.finrank ℝ (vectorSpan ℝ C) :=
    le_antisymm hDle hCle
  -- boundary
  have hriF : MapsTo F (intrinsicInterior ℝ D) (intrinsicInterior ℝ C) :=
    Plasticity.Topology.mapsTo_intrinsicInterior_of_injOn D C hDfin hfin hdim F hFcontD hFinjD (fun x hx => hx.2)
  have hriG : MapsTo G (intrinsicInterior ℝ C) (intrinsicInterior ℝ D) :=
    Plasticity.Topology.mapsTo_intrinsicInterior_of_injOn C D hfin hDfin hdim.symm G hGc hGinj hGD
  have hbd : A = intrinsicFrontier ℝ D := by
    ext x
    rw [frontier_eq_sdiff hDcl]
    constructor
    · rintro ⟨hxB, hxC⟩
      refine ⟨⟨hxB, hbdC hxC⟩, fun hri => ?_⟩
      have h1 := hriF hri
      rw [mem_preimage, frontier_eq_sdiff hCcl] at hxC
      exact hxC.2 h1
    · rintro ⟨hxD, hxri⟩
      refine ⟨hxD.1, ?_⟩
      rw [mem_preimage, frontier_eq_sdiff hCcl]
      refine ⟨hxD.2, fun h => hxri ?_⟩
      have h1 := hriG h
      rwa [hG2 x hxD.1] at h1
  -- Step 6: `D` is a face
  have hface : IsExtreme ℝ (closedBall (0 : X) 1) D := by
    refine ⟨inter_subset_left, ?_⟩
    intro x₁ hx₁ x₂ hx₂ x hxD hseg
    by_cases hxA : x ∈ A
    · exact hAD (hAe.left_mem_of_mem_openSegment hx₁ hx₂ hxA hseg)
    have hxri : x ∈ intrinsicInterior ℝ D := by
      by_contra h
      apply hxA
      rw [hbd, frontier_eq_sdiff hDcl]
      exact ⟨hxD, h⟩
    obtain ⟨ε, hε, hball⟩ := (Plasticity.Topology.mem_intrinsicInterior_iff_ball D x).1 hxri
    obtain ⟨a₁, a₂, ha₁, ha₂, ha12, hxeq⟩ := hseg
    have hx1 : ‖x‖ ≤ 1 := mem_closedBall_zero_iff.mp hxD.1
    have hx₁1 : ‖x₁‖ ≤ 1 := mem_closedBall_zero_iff.mp hx₁
    have hx₂1 : ‖x₂‖ ≤ 1 := mem_closedBall_zero_iff.mp hx₂
    -- the direction `x₁ - x` lies in the span of `D`
    have hdir : x₁ - x ∈ vectorSpan ℝ D := by
      by_contra hnot
      set Ω : Set X := closedBall (0 : X) 1 ∩ closedBall x 1 ∩ closedBall (-x) 1 with hΩ
      have hΩconv : Convex ℝ Ω :=
        ((convex_closedBall _ _).inter (convex_closedBall _ _)).inter (convex_closedBall _ _)
      have hxD' : -F (-x) ∈ C := by
        have h1 : x ∈ D' := hDD' ▸ hxD
        exact h1.2
      have hΩV : ∀ w ∈ Ω, F w - 0 ∈ vectorSpan ℝ C := by
        intro w hw
        rw [sub_zero]
        refine two_balls F hlip hCconv hCext hxD.1 hxD.2 hxD.1 hxD' hw.1.1 ?_ ?_
        · have h1 := hw.1.2
          rw [mem_closedBall, dist_eq_norm, norm_sub_rev] at h1
          exact h1
        · have h1 := hw.2
          rw [mem_closedBall, dist_eq_norm, sub_neg_eq_add, add_comm] at h1
          exact h1
      obtain ⟨hΩfin, hΩle⟩ := Plasticity.Topology.finrank_vectorSpan_le_of_injOn Ω hΩconv F
        (hFcont.mono fun w hw => hw.1.1) (hbij.injOn.mono fun w hw => hw.1.1)
        (vectorSpan ℝ C) hfin 0 hΩV
      have h0Ω : (0 : X) ∈ Ω := by
        refine ⟨⟨mem_closedBall_self zero_le_one, ?_⟩, ?_⟩
        · rw [mem_closedBall, dist_eq_norm, zero_sub, norm_neg]
          exact hx1
        · rw [mem_closedBall, dist_eq_norm, sub_neg_eq_add, zero_add]
          exact hx1
      have hspanΩ : vectorSpan ℝ Ω = Submodule.span ℝ Ω := by
        rw [vectorSpan_eq_span_vsub_set_right ℝ h0Ω]
        congr 1
        ext w
        simp
      have hmemΩ : ∀ w : X, ‖w‖ ≤ 1 → ‖x - w‖ ≤ 1 → ‖x + w‖ ≤ 1 → w ∈ Ω := by
        intro w h1 h2 h3
        refine ⟨⟨mem_closedBall_zero_iff.mpr h1, ?_⟩, ?_⟩
        · rw [mem_closedBall, dist_eq_norm, norm_sub_rev]
          exact h2
        · rw [mem_closedBall, dist_eq_norm, sub_neg_eq_add, add_comm]
          exact h3
      have hWD : vectorSpan ℝ D ≤ vectorSpan ℝ Ω := by
        rw [hspanΩ]
        intro w hw
        rcases eq_or_ne w 0 with rfl | hw0
        · exact Submodule.zero_mem _
        have hwpos : 0 < ‖w‖ := norm_pos_iff.mpr hw0
        set δ : ℝ := min ε 1 / (2 * ‖w‖) with hδ
        have hδ0 : 0 < δ := by positivity
        have hδw : ‖δ • w‖ = min ε 1 / 2 := by
          rw [norm_smul, Real.norm_of_nonneg hδ0.le, hδ]
          field_simp
        have hmin1 : min ε 1 ≤ 1 := min_le_right _ _
        have hminε : min ε 1 ≤ ε := min_le_left _ _
        have hminpos : 0 < min ε 1 := lt_min hε one_pos
        have hp : x + δ • w ∈ D :=
          hball _ (Submodule.smul_mem _ δ hw) (by rw [hδw]; linarith)
        have hm : x + -(δ • w) ∈ D :=
          hball _ (Submodule.neg_mem _ (Submodule.smul_mem _ δ hw))
            (by rw [norm_neg, hδw]; linarith)
        have hmem : δ • w ∈ Ω := by
          apply hmemΩ
          · rw [hδw]
            linarith
          · rw [sub_eq_add_neg]
            exact mem_closedBall_zero_iff.mp hm.1
          · exact mem_closedBall_zero_iff.mp hp.1
        have h1 := Submodule.smul_mem (Submodule.span ℝ Ω) δ⁻¹ (Submodule.subset_span hmem)
        rwa [smul_smul, inv_mul_cancel₀ hδ0.ne', one_smul] at h1
      have hx₁Ω : x₁ - x ∈ vectorSpan ℝ Ω := by
        rw [hspanΩ]
        set w : X := (a₁ * a₂ / 2) • (x₁ - x₂) with hw
        have hwΩ : w ∈ Ω := by
          apply hmemΩ
          · rw [hw, norm_smul, Real.norm_of_nonneg (by positivity)]
            have h1 : ‖x₁ - x₂‖ ≤ 2 := (norm_sub_le _ _).trans (by linarith)
            have h2 : a₁ * a₂ ≤ 1 := by nlinarith
            nlinarith [norm_nonneg (x₁ - x₂), mul_pos ha₁ ha₂]
          · have h1 : x - w = (a₁ * (1 - a₂ / 2)) • x₁ + (a₂ * (1 + a₁ / 2)) • x₂ := by
              rw [hw, ← hxeq]
              module
            rw [h1, ← mem_closedBall_zero_iff]
            refine (convex_closedBall (0 : X) 1) hx₁ hx₂ ?_ ?_ ?_
            · nlinarith
            · positivity
            · linear_combination ha12
          · have h1 : x + w = (a₁ * (1 + a₂ / 2)) • x₁ + (a₂ * (1 - a₁ / 2)) • x₂ := by
              rw [hw, ← hxeq]
              module
            rw [h1, ← mem_closedBall_zero_iff]
            refine (convex_closedBall (0 : X) 1) hx₁ hx₂ ?_ ?_ ?_
            · positivity
            · nlinarith
            · linear_combination ha12
        have hx₁w : x₁ - x = (2 / a₁) • w := by
          rw [hw, ← hxeq, smul_smul]
          have h1 : 2 / a₁ * (a₁ * a₂ / 2) = a₂ := by field_simp
          rw [h1]
          have h2 : a₂ = 1 - a₁ := by linarith
          rw [h2]
          module
        rw [hx₁w]
        exact Submodule.smul_mem _ _ (Submodule.subset_span hwΩ)
      have hlt : vectorSpan ℝ D < vectorSpan ℝ Ω :=
        lt_of_le_of_ne hWD (fun h => hnot (h ▸ hx₁Ω))
      have h1 := Submodule.finrank_lt_finrank_of_lt hlt
      omega
    -- the segment from `x` towards `x₁` leaves `D` through `A`
    by_contra hx₁D
    set T : Set ℝ := {s | s ∈ Icc (0 : ℝ) 1 ∧ x + s • (x₁ - x) ∈ D} with hT
    have hTcl : IsClosed T := by
      have hc : Continuous (fun s : ℝ => x + s • (x₁ - x)) := by fun_prop
      exact isClosed_Icc.inter (hDcl.preimage hc)
    have hTbdd : BddAbove T := ⟨1, fun s hs => hs.1.2⟩
    have hTne : T.Nonempty := ⟨0, ⟨le_refl _, zero_le_one⟩, by simpa using hxD⟩
    set s₀ := sSup T with hs₀
    have hs₀T : s₀ ∈ T := hTcl.csSup_mem hTne hTbdd
    have hs₀1 : s₀ < 1 := by
      rcases eq_or_lt_of_le hs₀T.1.2 with h | h
      · exfalso
        apply hx₁D
        have h1 := hs₀T.2
        rw [h, one_smul, add_sub_cancel] at h1
        exact h1
      · exact h
    have hs₀0 : 0 ≤ s₀ := hs₀T.1.1
    set y := x + s₀ • (x₁ - x) with hy
    have hyD : y ∈ D := hs₀T.2
    have hyri : y ∉ intrinsicInterior ℝ D := by
      intro hyri
      obtain ⟨ε', hε', hball'⟩ := (Plasticity.Topology.mem_intrinsicInterior_iff_ball D y).1 hyri
      set δ := min (1 - s₀) (ε' / (2 * (‖x₁ - x‖ + 1))) with hδ
      have hδ0 : 0 < δ := lt_min (by linarith) (by positivity)
      have hδ1 : δ ≤ 1 - s₀ := min_le_left _ _
      have hδ2 : δ ≤ ε' / (2 * (‖x₁ - x‖ + 1)) := min_le_right _ _
      have hδw : ‖δ • (x₁ - x)‖ < ε' := by
        rw [norm_smul, Real.norm_of_nonneg hδ0.le]
        have h1 : δ * (2 * (‖x₁ - x‖ + 1)) ≤ ε' := by
          rwa [le_div_iff₀ (by positivity)] at hδ2
        nlinarith [norm_nonneg (x₁ - x)]
      have hmem : y + δ • (x₁ - x) ∈ D :=
        hball' _ (Submodule.smul_mem _ _ hdir) hδw
      have hT' : s₀ + δ ∈ T := by
        refine ⟨⟨by linarith, by linarith⟩, ?_⟩
        have h1 : x + (s₀ + δ) • (x₁ - x) = y + δ • (x₁ - x) := by
          rw [hy, add_smul]
          abel
        rw [h1]
        exact hmem
      have h1 := le_csSup hTbdd hT'
      linarith
    have hyA : y ∈ A := by
      rw [hbd, frontier_eq_sdiff hDcl]
      exact ⟨hyD, hyri⟩
    have hyseg : y ∈ openSegment ℝ x₁ x₂ := by
      refine ⟨a₁ + s₀ * a₂, (1 - s₀) * a₂, by positivity,
        mul_pos (by linarith) ha₂, by linear_combination ha12, ?_⟩
      rw [hy, ← hxeq]
      have h2 : a₂ = 1 - a₁ := by linarith
      rw [h2]
      module
    exact hx₁D (hAD (hAe.left_mem_of_mem_openSegment hx₁ hx₂ hyA hyseg))
  -- the remaining fields
  have hDne : D.Nonempty := ⟨G c₀, hGD hc₀⟩
  have hDsph : D ⊆ sphere (0 : X) 1 := fun x hx => hFsph x hx.1 (hCsph hx.2)
  have hnegC : closedBall (0 : X) 1 ∩ F ⁻¹' (-C) = -D := by
    ext x
    rw [Set.mem_neg, hDD']
    simp only [hD', mem_ofPred_eq, mem_inter_iff, mem_preimage, Set.mem_neg, neg_neg,
      mem_closedBall_zero_iff, norm_neg]
  exact ⟨⟨hDne, hconvD, hDsph, hface⟩, hDc, hDfin, hdim, hnegC, hbd⟩
