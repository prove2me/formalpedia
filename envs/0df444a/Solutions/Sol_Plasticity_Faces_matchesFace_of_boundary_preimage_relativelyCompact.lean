-- Prove2me | solution 1 for Plasticity.Faces.matchesFace_of_boundary_preimage_relativelyCompact
-- status  : ACCEPTED   (prove)
-- author  : @scanstone
-- created : 2026-10-15T00:45:11.552985+00:00
-- url     : https://prove2.me/submissions/dee1846c-c616-4475-b764-042227bd4bf0

import Theorems.Thm_Plasticity_BallMap_map_zero_of_surjOn
import Theorems.Thm_Plasticity_BallMap_norm_map_le
import Theorems.Thm_Plasticity_BallMap_mem_sphere_of_map_mem_sphere
import Theorems.Thm_Plasticity_BallMap_norm_map_eq_of_mapsTo_sphere
import Theorems.Thm_Plasticity_BallMap_map_neg_of_map_mem_extremePoints
import Theorems.Thm_Plasticity_BallMap_mem_extremePoints_of_map_mem_extremePoints
import Theorems.Thm_Plasticity_BallMap_map_smul_of_map_mem_extremePoints
import Theorems.Thm_Plasticity_Faces_isCompact_and_eq_closedBall_inter_affineSpan
import Theorems.Thm_Plasticity_Aux_exists_proper_face
import Theorems.Thm_Plasticity_Topology_mem_intrinsicInterior_iff_ball
import Theorems.Thm_Plasticity_Faces_preimage_face_of_boundary_compact
import Theorems.Thm_Plasticity_Faces_image_smul_preimage_eq_smul
import Theorems.Thm_Plasticity_Faces_matchesFace_singleton
import Definitions.Def_Plasticity_Faces
import Mathlib.Topology.EMetricSpace.Lipschitz
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Convex.Intrinsic
import Mathlib.Tactic.Module

namespace Sol_Plasticity_Faces_matchesFace_of_boundary_preimage_relativelyCompact

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

end Sol_Plasticity_Faces_matchesFace_of_boundary_preimage_relativelyCompact


namespace Sol_Plasticity_Faces_matchesFace_of_boundary_preimage_relativelyCompact

open Set Metric

lemma frontier_eq_sdiff {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {C : Set E}
    (hC : IsClosed C) : intrinsicFrontier ℝ C = C \ intrinsicInterior ℝ C := by
  have hcl : intrinsicClosure ℝ C = C :=
    Subset.antisymm (intrinsicClosure_subset_closure.trans hC.closure_subset)
      subset_intrinsicClosure
  rw [← intrinsicClosure_sdiff_intrinsicInterior, hcl]

/-- A point of the relative boundary of a finite-dimensional closed convex set `C` lies in an
extreme subset `C'` of `C` of smaller dimension, and such a `C'` lies in the relative
boundary. -/
lemma exists_bd_face {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {C : Set E}
    (hCconv : Convex ℝ C) (hCcl : IsClosed C) (hfin : FiniteDimensional ℝ (vectorSpan ℝ C))
    {y : E} (hy : y ∈ intrinsicFrontier ℝ C) :
    ∃ C' : Set E, C' ⊆ C ∧ Convex ℝ C' ∧ IsExtreme ℝ C C' ∧ y ∈ C' ∧
      Module.finrank ℝ (vectorSpan ℝ C') < Module.finrank ℝ (vectorSpan ℝ C) ∧
      C' ⊆ intrinsicFrontier ℝ C := by
  rw [frontier_eq_sdiff hCcl] at hy ⊢
  obtain ⟨C', hC'C, hC'conv, hC'ext, hyC', hdim⟩ :=
    Plasticity.Aux.exists_proper_face C hCconv hfin y hy.1 hy.2
  refine ⟨C', hC'C, hC'conv, hC'ext, hyC', hdim, fun z hz => ⟨hC'C hz, fun hzri => ?_⟩⟩
  obtain ⟨ε, hε, hball⟩ := (Plasticity.Topology.mem_intrinsicInterior_iff_ball C z).1 hzri
  have hCC' : C ⊆ C' := by
    intro c hc
    rcases eq_or_ne c z with rfl | hcz
    · exact hz
    have hzc : 0 < ‖z - c‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hcz.symm)
    set δ := ε / (2 * ‖z - c‖) with hδ
    have hδ0 : 0 < δ := by positivity
    have hmem : z + δ • (z - c) ∈ C := by
      refine hball _ (Submodule.smul_mem _ _ (vsub_mem_vectorSpan ℝ (hC'C hz) hc)) ?_
      rw [norm_smul, Real.norm_of_nonneg hδ0.le, hδ]
      field_simp
      linarith
    have h1 : (1 + δ) ≠ 0 := by positivity
    have hseg : z ∈ openSegment ℝ c (z + δ • (z - c)) := by
      refine ⟨δ / (1 + δ), 1 / (1 + δ), by positivity, by positivity,
        by rw [← add_div, div_eq_one_iff_eq h1]; ring, ?_⟩
      have h2 : (δ / (1 + δ)) • c + (1 / (1 + δ)) • (z + δ • (z - c)) =
          ((1 + δ) / (1 + δ)) • z := by
        module
      rw [h2, div_self h1, one_smul]
    exact hC'ext.left_mem_of_mem_openSegment hc hmem hz hseg
  have hCeq : C' = C := Subset.antisymm hC'C hCC'
  rw [hCeq] at hdim
  exact lt_irrefl _ hdim

end Sol_Plasticity_Faces_matchesFace_of_boundary_preimage_relativelyCompact

open Set Metric Sol_Plasticity_Faces_matchesFace_of_boundary_preimage_relativelyCompact Plasticity in
open scoped Pointwise in
theorem solution {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (F : X → Y)
    (hbij : Set.BijOn F (Metric.closedBall (0 : X) 1) (Metric.closedBall (0 : Y) 1))
    (hlip : LipschitzOnWith 1 F (Metric.closedBall (0 : X) 1))
    (C : Set Y) (hC : IsSphereFace C) (hfin : FiniteDimensional ℝ (vectorSpan ℝ C))
    (ih : ∀ C' : Set Y, IsSphereFace C' → C' ⊆ C →
      Module.finrank ℝ (vectorSpan ℝ C') < Module.finrank ℝ (vectorSpan ℝ C) → MatchesFace F C')
    (htame : ∃ K : Set X, IsCompact K ∧
      Metric.closedBall (0 : X) 1 ∩ F ⁻¹' (intrinsicFrontier ℝ C) ⊆ K) :
    MatchesFace F C := by
  rcases Nat.eq_zero_or_pos (Module.finrank ℝ (vectorSpan ℝ C)) with h0 | hn
  · -- dimension 0: `C = {e}` for an extreme point `e` of the unit ball
    have hss : C.Subsingleton :=
      (vectorSpan_eq_bot_iff_subsingleton ℝ).mp (Submodule.finrank_eq_zero.mp h0)
    obtain ⟨e, he⟩ := hC.1
    obtain rfl := hss.eq_singleton_of_mem he
    exact Plasticity.Faces.matchesFace_singleton F hbij hlip e hC
  replace hn : 1 ≤ Module.finrank ℝ (vectorSpan ℝ C) := hn
  have hC' := hC
  obtain ⟨hCne, hCconv, hCsph, hCext⟩ := hC
  have hfin' := hfin
  obtain ⟨hCcpt, -⟩ := Plasticity.Faces.isCompact_and_eq_closedBall_inter_affineSpan C hC' hfin
  have hCcl : IsClosed C := hCcpt.isClosed
  have hbdC : intrinsicFrontier ℝ C ⊆ C := intrinsicFrontier_subset hCcl
  obtain ⟨-, -, -, hFext, -⟩ := Sol_Plasticity_Faces_matchesFace_of_boundary_preimage_relativelyCompact.ballMap_facts F hbij hlip
  have hFcont : ContinuousOn F (closedBall (0 : X) 1) := hlip.continuousOn
  set A := closedBall (0 : X) 1 ∩ F ⁻¹' intrinsicFrontier ℝ C with hA
  set D := closedBall (0 : X) 1 ∩ F ⁻¹' C with hD
  -- every boundary point of `C` lies in a good face of `B_Y` inside the boundary
  have hgood : ∀ y ∈ intrinsicFrontier ℝ C, ∃ C' : Set Y, MatchesFace F C' ∧ IsExtreme ℝ C C' ∧
      C' ⊆ intrinsicFrontier ℝ C ∧ y ∈ C' := by
    intro y hy
    obtain ⟨C', hC'C, hC'conv, hC'ext, hyC', hdim, hC'bd⟩ := exists_bd_face hCconv hCcl hfin hy
    have hC'sf : IsSphereFace C' :=
      ⟨⟨y, hyC'⟩, hC'conv, hC'C.trans hCsph, hCext.trans hC'ext⟩
    exact ⟨C', ih C' hC'sf hC'C hdim, hC'ext, hC'bd, hyC'⟩
  -- `A` is compact
  obtain ⟨K, hK, hAK⟩ := htame
  have hAcl : IsClosed A := by
    have : FiniteDimensional ℝ (affineSpan ℝ C).direction := by
      rw [direction_affineSpan]
      exact hfin
    exact hFcont.preimage_isClosed_of_isClosed isClosed_closedBall
      (isClosed_intrinsicFrontier (affineSpan ℝ C).closed_of_finiteDimensional)
  have hAc : IsCompact A := hK.of_isClosed_subset hAcl hAK
  -- `A` is an extreme subset of `B_X`
  have hAe : IsExtreme ℝ (closedBall (0 : X) 1) A := by
    refine ⟨inter_subset_left, ?_⟩
    intro x₁ hx₁ x₂ hx₂ x hx hseg
    obtain ⟨C', hgC', -, hC'bd, hxC'⟩ := hgood (F x) hx.2
    have hface := hgC'.1.2.2.2
    have h1 := hface.left_mem_of_mem_openSegment hx₁ hx₂ ⟨hx.1, hxC'⟩ hseg
    exact ⟨hx₁, hC'bd h1.2⟩
  -- `A` is symmetric: `A = -G(-∂C)`
  have hAs : ∀ x ∈ closedBall (0 : X) 1,
      F x ∈ intrinsicFrontier ℝ C ↔ -F (-x) ∈ intrinsicFrontier ℝ C := by
    intro x hx
    have hnx : -x ∈ closedBall (0 : X) 1 := by simpa using hx
    constructor
    · intro h
      obtain ⟨C', hgC', -, hC'bd, hxC'⟩ := hgood (F x) h
      have hneg := hgC'.2.2.2.2.1
      have h1 : -x ∈ -(closedBall (0 : X) 1 ∩ F ⁻¹' C') := by
        rw [Set.mem_neg, neg_neg]
        exact ⟨hx, hxC'⟩
      rw [← hneg] at h1
      have h2 : F (-x) ∈ -C' := h1.2
      rw [Set.mem_neg] at h2
      exact hC'bd h2
    · intro h
      obtain ⟨C', hgC', -, hC'bd, hxC'⟩ := hgood (-F (-x)) h
      have hneg := hgC'.2.2.2.2.1
      have h1 : -x ∈ closedBall (0 : X) 1 ∩ F ⁻¹' (-C') := by
        refine ⟨hnx, ?_⟩
        show F (-x) ∈ -C'
        rw [Set.mem_neg]
        exact hxC'
      rw [hneg, Set.mem_neg, neg_neg] at h1
      exact hC'bd h1.2
  -- Lemma 2 and Proposition 4
  obtain ⟨hDsf, hDc, hDfin, hdim, hnegD, hbd⟩ :=
    Plasticity.Faces.preimage_face_of_boundary_compact F hbij hlip C hC' hfin hAc hAe hAs
  have hscale := Plasticity.Faces.image_smul_preimage_eq_smul F hbij hlip C hC' hfin hDc
  have hDcl : IsClosed D := hDc.isClosed
  -- extreme points
  have hext : closedBall (0 : X) 1 ∩ F ⁻¹' (C.extremePoints ℝ) = D.extremePoints ℝ := by
    apply Subset.antisymm
    · rintro x ⟨hx, hFx⟩
      have h1 : F x ∈ (closedBall (0 : Y) 1).extremePoints ℝ :=
        hCext.extremePoints_subset_extremePoints hFx
      have h2 := (hFext x hx h1).1
      have hFxC : F x ∈ C := extremePoints_subset (show F x ∈ C.extremePoints ℝ from hFx)
      exact inter_extremePoints_subset_extremePoints_of_subset inter_subset_left
        ⟨⟨hx, hFxC⟩, h2⟩
    · intro x hx
      have hxD : x ∈ D := extremePoints_subset hx
      refine ⟨hxD.1, ?_⟩
      by_cases hFxbd : F x ∈ intrinsicFrontier ℝ C
      · obtain ⟨C', hgC', hC'ext, hC'bd, hxC'⟩ := hgood (F x) hFxbd
        have hextC' := hgC'.2.2.2.2.2.2.1
        have hD'D : closedBall (0 : X) 1 ∩ F ⁻¹' C' ⊆ D :=
          fun z hz => ⟨hz.1, hbdC (hC'bd hz.2)⟩
        have h1 : x ∈ (closedBall (0 : X) 1 ∩ F ⁻¹' C').extremePoints ℝ :=
          inter_extremePoints_subset_extremePoints_of_subset hD'D ⟨⟨hxD.1, hxC'⟩, hx⟩
        rw [← hextC'] at h1
        exact hC'ext.extremePoints_subset_extremePoints h1.2
      · exfalso
        have hxri : x ∈ intrinsicInterior ℝ D := by
          by_contra h
          apply hFxbd
          have h1 : x ∈ intrinsicFrontier ℝ D := by
            rw [frontier_eq_sdiff hDcl]
            exact ⟨hxD, h⟩
          rw [← hbd] at h1
          exact h1.2
        obtain ⟨ε, hε, hball⟩ := (Plasticity.Topology.mem_intrinsicInterior_iff_ball D x).1 hxri
        have hpos : 0 < Module.finrank ℝ (vectorSpan ℝ D) := by rw [hdim]; omega
        have hne : vectorSpan ℝ D ≠ ⊥ := by
          intro h
          rw [h, finrank_bot] at hpos
          exact lt_irrefl _ hpos
        obtain ⟨w, hw, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
        have hwpos : 0 < ‖w‖ := norm_pos_iff.mpr hw0
        set δ := ε / (2 * ‖w‖) with hδ
        have hδ0 : 0 < δ := by positivity
        have hδw : ‖δ • w‖ < ε := by
          rw [norm_smul, Real.norm_of_nonneg hδ0.le, hδ]
          field_simp
          linarith
        have hp : x + δ • w ∈ D := hball _ (Submodule.smul_mem _ _ hw) hδw
        have hm : x + -(δ • w) ∈ D :=
          hball _ (Submodule.neg_mem _ (Submodule.smul_mem _ _ hw)) (by rwa [norm_neg])
        have hseg : x ∈ openSegment ℝ (x + δ • w) (x + -(δ • w)) := by
          refine ⟨1 / 2, 1 / 2, by norm_num, by norm_num, by norm_num, ?_⟩
          module
        have h1 := hx.2 hp hm hseg
        have h2 : δ • w = 0 := by
          have h3 : x + δ • w - x = 0 := by rw [h1, sub_self]
          simpa using h3
        rcases smul_eq_zero.mp h2 with h | h
        · exact hδ0.ne' h
        · exact hw0 h
  exact ⟨hDsf, hDc, hDfin, hdim, hnegD, hbd, hext, hscale⟩
