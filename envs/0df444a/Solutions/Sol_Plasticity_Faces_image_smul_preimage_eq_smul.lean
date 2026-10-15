-- Prove2me | solution 1 for Plasticity.Faces.image_smul_preimage_eq_smul
-- status  : ACCEPTED   (prove)
-- author  : @scanstone
-- created : 2026-10-15T00:41:24.324989+00:00
-- url     : https://prove2.me/submissions/585bfc6a-6d6f-45cf-bf56-0a5f1ec7ebeb

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
import Theorems.Thm_Plasticity_Topology_exists_closedBall_model_of_convex_compact
import Theorems.Thm_Plasticity_Topology_closedBall_subset_image_of_eqOn_sphere
import Theorems.Thm_Plasticity_Faces_matchesFace_singleton
import Definitions.Def_Plasticity_Faces
import Mathlib.Topology.EMetricSpace.Lipschitz
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Module.RCLike.Real
import Mathlib.Analysis.Convex.Segment
import Mathlib.Topology.Order.Monotone

namespace Sol_Plasticity_Faces_image_smul_preimage_eq_smul

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

end Sol_Plasticity_Faces_image_smul_preimage_eq_smul


namespace Sol_Plasticity_Faces_image_smul_preimage_eq_smul

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

/-- (K5): if `F x` lies in an extreme subset `C'` of the ball, so does `τ⁻¹ F (τ x)`. -/
lemma K5 (F : X → Y) (hFnorm : ∀ x ∈ closedBall (0 : X) 1, ‖F x‖ ≤ ‖x‖)
    (hlip : LipschitzOnWith 1 F (closedBall (0 : X) 1)) {C' : Set Y}
    (hC' : IsExtreme ℝ (closedBall (0 : Y) 1) C') {x : X} (hx : x ∈ closedBall (0 : X) 1)
    (hFx : F x ∈ C') {τ : ℝ} (hτ0 : 0 < τ) (hτ1 : τ ≤ 1) : τ⁻¹ • F (τ • x) ∈ C' := by
  rcases eq_or_lt_of_le hτ1 with rfl | hτ1'
  · simpa using hFx
  have hx1 := mem_closedBall_zero_iff.mp hx
  have hτx_norm : ‖τ • x‖ = τ * ‖x‖ := by rw [norm_smul, Real.norm_of_nonneg hτ0.le]
  have hτx : τ • x ∈ closedBall (0 : X) 1 := by
    rw [mem_closedBall_zero_iff, hτx_norm]
    nlinarith [norm_nonneg x]
  have hw : ‖F (τ • x)‖ ≤ τ := (hFnorm _ hτx).trans (by rw [hτx_norm]; nlinarith [norm_nonneg x])
  have hFxw : ‖F x - F (τ • x)‖ ≤ 1 - τ := by
    have h1 := hlip.dist_le_mul x hx (τ • x) hτx
    simp only [NNReal.coe_one, one_mul, dist_eq_norm] at h1
    have h2 : x - τ • x = (1 - τ) • x := by rw [sub_smul, one_smul]
    rw [h2, norm_smul, Real.norm_of_nonneg (by linarith)] at h1
    nlinarith [norm_nonneg x]
  have h1τ : 0 < 1 - τ := by linarith
  have hp : τ⁻¹ • F (τ • x) ∈ closedBall (0 : Y) 1 := by
    rw [mem_closedBall_zero_iff, norm_smul, norm_inv, Real.norm_of_nonneg hτ0.le,
      inv_mul_le_iff₀ hτ0]
    linarith
  have hq : (1 - τ)⁻¹ • (F x - F (τ • x)) ∈ closedBall (0 : Y) 1 := by
    rw [mem_closedBall_zero_iff, norm_smul, norm_inv, Real.norm_of_nonneg h1τ.le,
      inv_mul_le_iff₀ h1τ]
    linarith
  have hseg : F x ∈ openSegment ℝ (τ⁻¹ • F (τ • x)) ((1 - τ)⁻¹ • (F x - F (τ • x))) := by
    refine ⟨τ, 1 - τ, hτ0, h1τ, by ring, ?_⟩
    rw [smul_smul, smul_smul, mul_inv_cancel₀ hτ0.ne', mul_inv_cancel₀ h1τ.ne', one_smul,
      one_smul]
    abel
  exact hC'.left_mem_of_mem_openSegment hp hq hFx hseg

/-- A point of the relative boundary of a finite-dimensional closed convex extreme subset `C`
of the ball lies in an extreme subset of the ball contained in the relative boundary. -/
lemma exists_bd_face {C : Set Y} (hCconv : Convex ℝ C) (hCcl : IsClosed C)
    (hfin : FiniteDimensional ℝ (vectorSpan ℝ C)) (hCext : IsExtreme ℝ (closedBall (0 : Y) 1) C)
    {y : Y} (hy : y ∈ intrinsicFrontier ℝ C) :
    ∃ C' : Set Y, IsExtreme ℝ (closedBall (0 : Y) 1) C' ∧ C' ⊆ intrinsicFrontier ℝ C ∧
      y ∈ C' := by
  rw [frontier_eq_sdiff hCcl] at hy ⊢
  obtain ⟨C', hC'C, -, hC'ext, hyC', hdim⟩ :=
    Plasticity.Aux.exists_proper_face C hCconv hfin y hy.1 hy.2
  refine ⟨C', hCext.trans hC'ext, fun z hz => ⟨hC'C hz, fun hzri => ?_⟩, hyC'⟩
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

end Sol_Plasticity_Faces_image_smul_preimage_eq_smul

open Set Metric Topology Filter Sol_Plasticity_Faces_image_smul_preimage_eq_smul Plasticity in
open scoped Pointwise in
theorem solution {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (F : X → Y)
    (hbij : Set.BijOn F (Metric.closedBall (0 : X) 1) (Metric.closedBall (0 : Y) 1))
    (hlip : LipschitzOnWith 1 F (Metric.closedBall (0 : X) 1))
    (C : Set Y) (hC : IsSphereFace C) (hfin : FiniteDimensional ℝ (vectorSpan ℝ C))
    (hD : IsCompact (Metric.closedBall (0 : X) 1 ∩ F ⁻¹' C)) :
    ∀ t ∈ Set.Icc (0 : ℝ) 1,
      F '' (t • (Metric.closedBall (0 : X) 1 ∩ F ⁻¹' C)) = t • C := by
  rcases Nat.eq_zero_or_pos (Module.finrank ℝ (vectorSpan ℝ C)) with h0 | hn
  · -- dimension 0: `C = {e}` for an extreme point `e` of the unit ball
    have hss : C.Subsingleton :=
      (vectorSpan_eq_bot_iff_subsingleton ℝ).mp (Submodule.finrank_eq_zero.mp h0)
    obtain ⟨e, he⟩ := hC.1
    obtain rfl := hss.eq_singleton_of_mem he
    exact (Plasticity.Faces.matchesFace_singleton F hbij hlip e hC).2.2.2.2.2.2.2
  replace hn : 1 ≤ Module.finrank ℝ (vectorSpan ℝ C) := hn
  have hC' := hC
  obtain ⟨hCne, hCconv, hCsph, hCext⟩ := hC
  have hfin' := hfin
  obtain ⟨hCcpt, -⟩ := Plasticity.Faces.isCompact_and_eq_closedBall_inter_affineSpan C hC' hfin
  have hCcl : IsClosed C := hCcpt.isClosed
  have hbdC : intrinsicFrontier ℝ C ⊆ C := intrinsicFrontier_subset hCcl
  have hCB : C ⊆ closedBall (0 : Y) 1 := hCext.subset
  obtain ⟨hF0, hFnorm, -, -, -⟩ := Sol_Plasticity_Faces_image_smul_preimage_eq_smul.ballMap_facts F hbij hlip
  have hFcont : ContinuousOn F (closedBall (0 : X) 1) := hlip.continuousOn
  set D := closedBall (0 : X) 1 ∩ F ⁻¹' C with hDdef
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
    hFD ▸ contOn_leftInv hD (hFcont.mono inter_subset_left) (fun x hx => hG2 x hx.1)
  have hDne : D.Nonempty := by
    obtain ⟨c, hc⟩ := hCne
    exact ⟨G c, hGD hc⟩
  intro t ht
  rcases eq_or_lt_of_le ht.1 with h0 | ht0
  · -- `t = 0`
    rw [← h0]
    ext y
    simp only [mem_image, Set.mem_smul_set, zero_smul]
    constructor
    · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
      obtain ⟨c, hc⟩ := hCne
      exact ⟨c, hc, hF0.symm⟩
    · rintro ⟨c, hc, rfl⟩
      obtain ⟨x, hx⟩ := hDne
      exact ⟨0, ⟨x, hx, rfl⟩, hF0⟩
  have ht1 := ht.2
  have htD : ∀ x ∈ D, t • x ∈ closedBall (0 : X) 1 := by
    intro x hx
    rw [mem_closedBall_zero_iff, norm_smul, Real.norm_of_nonneg ht0.le]
    have := mem_closedBall_zero_iff.mp hx.1
    nlinarith [norm_nonneg x]
  apply Subset.antisymm
  · rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    have h1 := K5 F hFnorm hlip hCext hx.1 hx.2 ht0 ht1
    refine ⟨t⁻¹ • F (t • x), h1, ?_⟩
    simp only [smul_smul, mul_inv_cancel₀ ht0.ne', one_smul]
  -- the ball model of `C` and the parametrization `β` of `D`
  obtain ⟨φ, ψ, hφc, hψc, hφ, hψ⟩ := Plasticity.Topology.exists_closedBall_model_of_convex_compact C hCcpt hCconv hCne hfin
  have hpos : 0 < Module.finrank ℝ (vectorSpan ℝ C) := by omega
  have hVnt : Nontrivial (vectorSpan ℝ C) := Module.nontrivial_of_finrank_pos hpos
  set β : vectorSpan ℝ C → X := fun z => G (φ z) with hβ
  have hβc : ContinuousOn β (closedBall 0 1) :=
    hGc.comp hφc.continuousOn (fun z hz => (hφ z (mem_closedBall_zero_iff.mp hz)).1)
  have hβD : ∀ z : vectorSpan ℝ C, ‖z‖ ≤ 1 → β z ∈ D := fun z hz => hGD (hφ z hz).1
  have hFβ : ∀ z : vectorSpan ℝ C, ‖z‖ ≤ 1 → F (β z) = φ z :=
    fun z hz => (hG1 _ (hCB (hφ z hz).1)).2
  -- the homotopy from `x ↦ t⁻¹ F (t x)` to `F`, packed into one map of the ball
  set σ : vectorSpan ℝ C → ℝ := fun z => max 1 (2 * ‖z‖) with hσ
  set τ : vectorSpan ℝ C → ℝ := fun z => t + (1 - t) * (σ z - 1) with hτ
  set ρ : vectorSpan ℝ C → vectorSpan ℝ C := fun z => (2 / σ z) • z with hρ
  have hσ1 : ∀ z, 1 ≤ σ z := fun z => le_max_left _ _
  have hσ2 : ∀ z, 2 * ‖z‖ ≤ σ z := fun z => le_max_right _ _
  have hσle : ∀ z : vectorSpan ℝ C, ‖z‖ ≤ 1 → σ z ≤ 2 :=
    fun z hz => max_le (by norm_num) (by linarith)
  have hτt : ∀ z, t ≤ τ z := by
    intro z
    have := hσ1 z
    simp only [hτ]
    nlinarith
  have hτ1 : ∀ z : vectorSpan ℝ C, ‖z‖ ≤ 1 → τ z ≤ 1 := by
    intro z hz
    have := hσle z hz
    simp only [hτ]
    nlinarith
  have hτ0 : ∀ z, 0 < τ z := fun z => lt_of_lt_of_le ht0 (hτt z)
  have hρnorm : ∀ z, ‖ρ z‖ = 2 * ‖z‖ / σ z := by
    intro z
    have := hσ1 z
    rw [hρ, norm_smul, Real.norm_of_nonneg (by positivity)]
    ring
  have hρB : ∀ z, ‖ρ z‖ ≤ 1 := by
    intro z
    rw [hρnorm, div_le_one (by linarith [hσ1 z])]
    exact hσ2 z
  have hρsph : ∀ z : vectorSpan ℝ C, 1 / 2 ≤ ‖z‖ → ‖ρ z‖ = 1 := by
    intro z hz
    have h1 : σ z = 2 * ‖z‖ := max_eq_right (by linarith)
    rw [hρnorm, h1, div_self (by positivity)]
  have hsmall : ∀ z : vectorSpan ℝ C, ‖z‖ ≤ 1 / 2 → τ z = t ∧ ρ z = (2 : ℝ) • z := by
    intro z hz
    have h1 : σ z = 1 := max_eq_left (by linarith)
    refine ⟨by simp only [hτ, h1]; ring, by simp only [hρ, h1]; norm_num⟩
  have hone : ∀ z : vectorSpan ℝ C, ‖z‖ = 1 → τ z = 1 ∧ ρ z = z := by
    intro z hz
    have h1 : σ z = 2 := by simp only [hσ, hz]; norm_num
    refine ⟨by simp only [hτ, h1]; ring, by simp only [hρ, h1]; norm_num⟩
  have hσc : Continuous σ := by fun_prop
  have hτc : Continuous τ := by fun_prop
  have hρc : Continuous ρ :=
    (continuous_const.div hσc (fun z => (lt_of_lt_of_le one_pos (hσ1 z)).ne')).smul
      continuous_id
  set g : vectorSpan ℝ C → vectorSpan ℝ C := fun z => ψ ((τ z)⁻¹ • F (τ z • β (ρ z))) with hg
  have hinB : ∀ z : vectorSpan ℝ C, ‖z‖ ≤ 1 → τ z • β (ρ z) ∈ closedBall (0 : X) 1 := by
    intro z hz
    have h1 := mem_closedBall_zero_iff.mp (hβD _ (hρB z)).1
    rw [mem_closedBall_zero_iff, norm_smul, Real.norm_of_nonneg (hτ0 z).le]
    have h2 := hτ1 z hz
    nlinarith [norm_nonneg (β (ρ z)), hτ0 z]
  have hgc : ContinuousOn g (closedBall 0 1) := by
    have hβρ : ContinuousOn (fun z => β (ρ z)) (closedBall 0 1) :=
      hβc.comp hρc.continuousOn (fun z _ => mem_closedBall_zero_iff.mpr (hρB z))
    have hinner : ContinuousOn (fun z => τ z • β (ρ z)) (closedBall 0 1) :=
      hτc.continuousOn.smul hβρ
    have hFin : ContinuousOn (fun z => F (τ z • β (ρ z))) (closedBall 0 1) :=
      hFcont.comp hinner (fun z hz => hinB z (mem_closedBall_zero_iff.mp hz))
    exact hψc.comp_continuousOn
      ((hτc.continuousOn.inv₀ (fun z _ => (hτ0 z).ne')).smul hFin)
  have hgid : ∀ z ∈ sphere (0 : vectorSpan ℝ C) 1, g z = z := by
    intro z hz
    have hz1 := mem_sphere_zero_iff_norm.mp hz
    obtain ⟨h1, h2⟩ := hone z hz1
    simp only [hg, h1, h2, inv_one, one_smul]
    rw [hFβ z hz1.le]
    exact (hφ z hz1.le).2.1
  have honto := Plasticity.Topology.closedBall_subset_image_of_eqOn_sphere g hgc hgid
  have hΦC : ∀ z : vectorSpan ℝ C, ‖z‖ ≤ 1 → (τ z)⁻¹ • F (τ z • β (ρ z)) ∈ C := by
    intro z hz
    have hb := hβD _ (hρB z)
    exact K5 F hFnorm hlip hCext hb.1 hb.2 (hτ0 z) (hτ1 z hz)
  have hgbd : ∀ z : vectorSpan ℝ C, ‖z‖ ≤ 1 → 1 / 2 ≤ ‖z‖ → ‖g z‖ = 1 := by
    intro z hz hz2
    have hρ1 := hρsph z hz2
    have hb := hβD _ (hρB z)
    have hFb : F (β (ρ z)) ∈ intrinsicFrontier ℝ C := by
      rw [hFβ _ (hρB z)]
      exact (hφ _ (hρB z)).2.2.mpr hρ1
    obtain ⟨C', hC'ext, hC'bd, hFbC'⟩ := exists_bd_face hCconv hCcl hfin hCext hFb
    have hy := hC'bd (K5 F hFnorm hlip hC'ext hb.1 hFbC' (hτ0 z) (hτ1 z hz))
    obtain ⟨hψ1, hψ2⟩ := hψ _ (hbdC hy)
    have h3 := (hφ _ hψ1).2.2
    rw [hψ2] at h3
    exact h3.mp hy
  -- points `c` with `‖ψ c‖ < 1`
  have hint : ∀ c ∈ C, ‖ψ c‖ < 1 → t • c ∈ F '' (t • D) := by
    intro c hc hψc1
    obtain ⟨z, hz, hgz⟩ := honto (mem_closedBall_zero_iff.mpr hψc1.le)
    have hz1 := mem_closedBall_zero_iff.mp hz
    have hz2 : ‖z‖ < 1 / 2 := by
      by_contra h
      push Not at h
      have h1 := hgbd z hz1 h
      rw [hgz] at h1
      linarith
    obtain ⟨hτz, hρz⟩ := hsmall z hz2.le
    have hceq : c = (τ z)⁻¹ • F (τ z • β (ρ z)) := by
      rw [← (hψ c hc).2, ← (hψ _ (hΦC z hz1)).2]
      congr 1
      exact hgz.symm
    rw [hτz] at hceq
    refine ⟨t • β (ρ z), ⟨β (ρ z), hβD _ (hρB z), rfl⟩, ?_⟩
    rw [hceq, smul_smul, mul_inv_cancel₀ ht0.ne', one_smul]
  -- all points of `C`, by approximation
  have hclosed : IsClosed (F '' (t • D)) := by
    have h1 : IsCompact (t • D) := hD.smul t
    exact (h1.image_of_continuousOn (hFcont.mono (by
      rintro _ ⟨x, hx, rfl⟩
      exact htD x hx))).isClosed
  rintro _ ⟨c, hc, rfl⟩
  obtain ⟨hψc1, hψc2⟩ := hψ c hc
  have hlim : Tendsto (fun s : ℝ => t • φ (s • ψ c)) (𝓝[<] 1) (𝓝 (t • c)) := by
    have hcont : Continuous (fun s : ℝ => t • φ (s • ψ c)) := by fun_prop
    have h1 := hcont.tendsto 1
    simp only [one_smul, hψc2] at h1
    exact h1.mono_left nhdsWithin_le_nhds
  apply hclosed.mem_of_tendsto hlim
  filter_upwards [Ioo_mem_nhdsLT (by norm_num : (0 : ℝ) < 1)] with s hs
  have hsw : ‖s • ψ c‖ ≤ 1 := by
    rw [norm_smul, Real.norm_of_nonneg hs.1.le]
    calc s * ‖ψ c‖ ≤ s * 1 := mul_le_mul_of_nonneg_left hψc1 hs.1.le
      _ ≤ 1 := by linarith [hs.2]
  have hsw' : ‖s • ψ c‖ < 1 := by
    rw [norm_smul, Real.norm_of_nonneg hs.1.le]
    calc s * ‖ψ c‖ ≤ s * 1 := mul_le_mul_of_nonneg_left hψc1 hs.1.le
      _ < 1 := by linarith [hs.2]
  obtain ⟨h1, h2, -⟩ := hφ _ hsw
  apply hint _ h1
  rw [h2]
  exact hsw'
