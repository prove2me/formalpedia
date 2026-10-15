-- Prove2me | solution 1 for Plasticity.Faces.reflected_preimage_eq_cone
-- status  : ACCEPTED   (prove)
-- author  : @scanstone
-- created : 2026-10-15T00:42:36.372894+00:00
-- url     : https://prove2.me/submissions/52fd0a4d-ae34-4c83-8a85-18719af0f4b1

import Theorems.Thm_Plasticity_BallMap_map_zero_of_surjOn
import Theorems.Thm_Plasticity_BallMap_norm_map_le
import Theorems.Thm_Plasticity_BallMap_mem_sphere_of_map_mem_sphere
import Theorems.Thm_Plasticity_BallMap_norm_map_eq_of_mapsTo_sphere
import Theorems.Thm_Plasticity_BallMap_map_neg_of_map_mem_extremePoints
import Theorems.Thm_Plasticity_BallMap_mem_extremePoints_of_map_mem_extremePoints
import Theorems.Thm_Plasticity_BallMap_map_smul_of_map_mem_extremePoints
import Theorems.Thm_Plasticity_Faces_isCompact_and_eq_closedBall_inter_affineSpan
import Theorems.Thm_Plasticity_Topology_exists_closedBall_model_of_convex_compact
import Theorems.Thm_Plasticity_Topology_isOpen_image_of_injOn_of_finrank_eq
import Theorems.Thm_Plasticity_Topology_closedBall_subset_image_of_eqOn_sphere
import Definitions.Def_Plasticity_Faces
import Mathlib.Topology.EMetricSpace.Lipschitz
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Module.RCLike.Real
import Mathlib.Analysis.LocallyConvex.HahnBanach
import Mathlib.Analysis.Convex.Segment

namespace Sol_Plasticity_Faces_reflected_preimage_eq_cone

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

end Sol_Plasticity_Faces_reflected_preimage_eq_cone


namespace Sol_Plasticity_Faces_reflected_preimage_eq_cone

open Set Metric Topology

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

/-- Step 1 of Lemma 2 along the segment `t (u - v)`, `0 ≤ t ≤ 1/4`. -/
lemma two_balls_t (F : X → Y) (hlip : LipschitzOnWith 1 F (closedBall (0 : X) 1)) {C : Set Y}
    (hconv : Convex ℝ C) (hext : IsExtreme ℝ (closedBall (0 : Y) 1) C) {u v : X}
    (hu : u ∈ closedBall (0 : X) 1) (hFu : F u ∈ C) (hv : v ∈ closedBall (0 : X) 1)
    (hFv : -F (-v) ∈ C) {t : ℝ} (ht0 : 0 ≤ t) (ht : t ≤ 1 / 4) :
    F (t • (u - v)) ∈ vectorSpan ℝ C := by
  have hu' := mem_closedBall_zero_iff.mp hu
  have hv' := mem_closedBall_zero_iff.mp hv
  apply two_balls F hlip hconv hext hu hFu hv hFv
  · rw [mem_closedBall_zero_iff, norm_smul, Real.norm_of_nonneg ht0]
    have h1 : ‖u - v‖ ≤ 2 := (norm_sub_le u v).trans (by linarith)
    nlinarith
  · have h1 : u - t • (u - v) = (1 - t) • u + t • v := by
      rw [smul_sub, sub_smul, one_smul]
      abel
    rw [h1, ← mem_closedBall_zero_iff]
    exact (convex_closedBall (0 : X) 1) hu hv (by linarith) ht0 (by ring)
  · have h1 : v + t • (u - v) = (1 - t) • v + t • u := by
      rw [smul_sub, sub_smul, one_smul]
      abel
    rw [h1, ← mem_closedBall_zero_iff]
    exact (convex_closedBall (0 : X) 1) hv hu (by linarith) ht0 (by ring)

section cone

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

lemma norm_normalize {z : V} (hz : z ≠ 0) : ‖‖z‖⁻¹ • z‖ = 1 := by
  rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (norm_ne_zero_iff.mpr hz)]

lemma normalize_smul (z : V) : ‖z‖ • (‖z‖⁻¹ • z) = z := by
  rcases eq_or_ne z 0 with rfl | hz
  · simp
  · rw [smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hz), one_smul]

/-- The cone map over `α` with apex `u`. -/
noncomputable def cm (α : V → X) (u : X) (z : V) : X := u + ‖z‖ • (α (‖z‖⁻¹ • z) - u)

lemma cm_zero (α : V → X) (u : X) : cm α u 0 = u := by simp [cm]

lemma cm_sphere (α : V → X) (u : X) {z : V} (hz : ‖z‖ = 1) : cm α u z = α z := by
  simp [cm, hz]

lemma cm_smul (α : V → X) (u : X) {z : V} (hz : ‖z‖ = 1) {s : ℝ} (hs : 0 < s) :
    cm α u (s • z) = u + s • (α z - u) := by
  have h1 : ‖s • z‖ = s := by rw [norm_smul, hz, mul_one, Real.norm_of_nonneg hs.le]
  have h2 : ‖s • z‖⁻¹ • (s • z) = z := by rw [h1, smul_smul, inv_mul_cancel₀ hs.ne', one_smul]
  simp only [cm, h2]
  rw [h1]

lemma cm_sub (α : V → X) (u : X) (z : V) :
    (1 / 4 : ℝ) • (u - cm α u z) = (‖z‖ / 4) • (u - α (‖z‖⁻¹ • z)) := by
  have h1 : u - cm α u z = ‖z‖ • (u - α (‖z‖⁻¹ • z)) := by
    simp only [cm]
    rw [smul_sub, smul_sub]
    abel
  rw [h1, smul_smul]
  congr 1
  ring

lemma cm_norm (α : V → X) {u : X} (hαB : ∀ z ∈ sphere (0 : V) 1, ‖α z‖ ≤ 1) (hu : ‖u‖ ≤ 1)
    {z : V} (hz : ‖z‖ ≤ 1) : ‖cm α u z‖ ≤ 1 := by
  rcases eq_or_ne z 0 with rfl | hz0
  · rw [cm_zero]
    exact hu
  have ha := hαB _ (mem_sphere_zero_iff_norm.mpr (norm_normalize hz0))
  have h1 : cm α u z = (1 - ‖z‖) • u + ‖z‖ • α (‖z‖⁻¹ • z) := by
    simp only [cm]
    rw [smul_sub, sub_smul, one_smul]
    abel
  rw [h1, ← mem_closedBall_zero_iff]
  exact (convex_closedBall (0 : X) 1) (mem_closedBall_zero_iff.mpr hu)
    (mem_closedBall_zero_iff.mpr ha) (by linarith) (norm_nonneg _) (by ring)

lemma cm_cont (α : V → X) {u : X} (hαc : ContinuousOn α (sphere (0 : V) 1))
    (hαB : ∀ z ∈ sphere (0 : V) 1, ‖α z‖ ≤ 1) (hu : ‖u‖ ≤ 1) :
    ContinuousOn (cm α u) (closedBall (0 : V) 1) := by
  intro z hz
  rcases eq_or_ne z 0 with rfl | hz0
  · rw [Metric.continuousWithinAt_iff]
    intro ε hε
    refine ⟨ε / 2, by positivity, fun y _ hyd => ?_⟩
    rw [cm_zero, dist_eq_norm]
    simp only [cm, add_sub_cancel_left]
    rw [dist_zero_right] at hyd
    rcases eq_or_ne y 0 with rfl | hy0
    · simp [hε]
    have ha := hαB _ (mem_sphere_zero_iff_norm.mpr (norm_normalize hy0))
    calc ‖‖y‖ • (α (‖y‖⁻¹ • y) - u)‖ = ‖y‖ * ‖α (‖y‖⁻¹ • y) - u‖ := by
          rw [norm_smul, norm_norm]
      _ ≤ ‖y‖ * 2 := by
          gcongr
          exact (norm_sub_le _ _).trans (by linarith)
      _ < ε := by linarith
  · rw [← continuousWithinAt_sdiff_singleton (y := (0 : V))]
    have hnc : ContinuousAt (fun y : V => ‖y‖⁻¹ • y) z :=
      (continuous_norm.continuousAt.inv₀ (norm_ne_zero_iff.mpr hz0)).smul continuousAt_id
    have hmaps : MapsTo (fun y : V => ‖y‖⁻¹ • y) (closedBall (0 : V) 1 \ {0}) (sphere 0 1) :=
      fun y hy => mem_sphere_zero_iff_norm.mpr (norm_normalize hy.2)
    have h1 : ContinuousWithinAt (fun y => α (‖y‖⁻¹ • y)) (closedBall (0 : V) 1 \ {0}) z :=
      ContinuousWithinAt.comp (f := fun y : V => ‖y‖⁻¹ • y) (g := α)
        (hαc _ (hmaps ⟨hz, hz0⟩)) hnc.continuousWithinAt hmaps
    exact continuousWithinAt_const.add
      (continuous_norm.continuousWithinAt.smul (h1.sub continuousWithinAt_const))

/-- If `s₁ (a₁ - u) = s₂ (a₂ - u)` with `a₁, a₂ ∈ A`, `0 ≤ s₁ ≤ s₂`, and no point of a
half-open segment `[u, a)` lies in `A`, then `s₁ = s₂` and either `s₂ = 0` or `a₁ = a₂`. -/
lemma cone_core {A : Set X} {u : X} (hnotA : ∀ a ∈ A, ∀ l ∈ Ico (0 : ℝ) 1, u + l • (a - u) ∉ A)
    {a₁ a₂ : X} (ha₁ : a₁ ∈ A) (ha₂ : a₂ ∈ A) {s₁ s₂ : ℝ} (hs₁ : 0 ≤ s₁) (h12 : s₁ ≤ s₂)
    (heq : s₁ • (a₁ - u) = s₂ • (a₂ - u)) : s₁ = s₂ ∧ (s₂ = 0 ∨ a₁ = a₂) := by
  rcases eq_or_lt_of_le (hs₁.trans h12) with h0 | hpos
  · exact ⟨by linarith, Or.inl h0.symm⟩
  have ha₂eq : a₂ = u + (s₁ / s₂) • (a₁ - u) := by
    have h1 : a₂ - u = (s₁ / s₂) • (a₁ - u) := by
      rw [div_eq_inv_mul, ← smul_smul, heq, smul_smul, inv_mul_cancel₀ hpos.ne', one_smul]
    rw [← h1]
    abel
  have hl0 : 0 ≤ s₁ / s₂ := div_nonneg hs₁ hpos.le
  by_cases hl1 : s₁ / s₂ < 1
  · exact absurd (ha₂eq ▸ ha₂) (hnotA a₁ ha₁ _ ⟨hl0, hl1⟩)
  have hss : s₁ = s₂ := by
    have h2 : s₁ / s₂ ≤ 1 := (div_le_one hpos).mpr h12
    have h3 : s₁ / s₂ = 1 := le_antisymm h2 (not_lt.mp hl1)
    rwa [div_eq_one_iff_eq hpos.ne'] at h3
  refine ⟨hss, Or.inr ?_⟩
  rw [hss] at heq
  have h4 := smul_right_injective X hpos.ne' heq
  simpa using h4

lemma cm_inj (α : V → X) {u : X} {A : Set X} (hαA : MapsTo α (sphere (0 : V) 1) A)
    (hαinj : InjOn α (sphere (0 : V) 1))
    (hnotA : ∀ a ∈ A, ∀ l ∈ Ico (0 : ℝ) 1, u + l • (a - u) ∉ A) :
    InjOn (cm α u) (closedBall (0 : V) 1) := by
  have huA : u ∉ A := by
    intro hu
    have h1 := hnotA u hu 0 ⟨le_refl _, one_pos⟩
    simp at h1
    exact h1 hu
  have hsph : ∀ z : V, z ≠ 0 → ‖z‖⁻¹ • z ∈ sphere (0 : V) 1 :=
    fun z hz => mem_sphere_zero_iff_norm.mpr (norm_normalize hz)
  -- the zero case
  have hzero : ∀ z : V, z ≠ 0 → cm α u z ≠ u := by
    intro z hz h
    simp only [cm, add_eq_left] at h
    rcases smul_eq_zero.mp h with h1 | h1
    · exact hz (norm_eq_zero.mp h1)
    · rw [sub_eq_zero] at h1
      exact huA (h1 ▸ hαA (hsph z hz))
  intro z₁ hz₁ z₂ hz₂ h
  rcases eq_or_ne z₁ 0 with rfl | h1
  · rcases eq_or_ne z₂ 0 with rfl | h2
    · rfl
    · rw [cm_zero] at h
      exact absurd h.symm (hzero z₂ h2)
  rcases eq_or_ne z₂ 0 with rfl | h2
  · rw [cm_zero] at h
    exact absurd h (hzero z₁ h1)
  have heq : ‖z₁‖ • (α (‖z₁‖⁻¹ • z₁) - u) = ‖z₂‖ • (α (‖z₂‖⁻¹ • z₂) - u) := by
    simp only [cm] at h
    exact add_left_cancel h
  have ha₁ := hαA (hsph z₁ h1)
  have ha₂ := hαA (hsph z₂ h2)
  have key : ‖z₁‖ = ‖z₂‖ ∧ α (‖z₁‖⁻¹ • z₁) = α (‖z₂‖⁻¹ • z₂) := by
    rcases le_total ‖z₁‖ ‖z₂‖ with hle | hle
    · obtain ⟨hs, hor⟩ := cone_core hnotA ha₁ ha₂ (norm_nonneg _) hle heq
      rcases hor with h0 | ha
      · exact absurd (norm_eq_zero.mp h0) h2
      · exact ⟨hs, ha⟩
    · obtain ⟨hs, hor⟩ := cone_core hnotA ha₂ ha₁ (norm_nonneg _) hle heq.symm
      rcases hor with h0 | ha
      · exact absurd (norm_eq_zero.mp h0) h1
      · exact ⟨hs.symm, ha.symm⟩
  have hdir := hαinj (hsph z₁ h1) (hsph z₂ h2) key.2
  rw [← normalize_smul z₁, ← normalize_smul z₂, hdir, key.1]

lemma cm_image (α : V → X) (u : X) {A : Set X} (hαA : MapsTo α (sphere (0 : V) 1) A)
    (hαonto : ∀ a ∈ A, ∃ z ∈ sphere (0 : V) 1, α z = a) (hne : (sphere (0 : V) 1).Nonempty) :
    cm α u '' closedBall (0 : V) 1 = {x | ∃ a ∈ A, x ∈ segment ℝ u a} := by
  ext x
  constructor
  · rintro ⟨z, hz, rfl⟩
    rcases eq_or_ne z 0 with rfl | hz0
    · obtain ⟨z₀, hz₀⟩ := hne
      exact ⟨α z₀, hαA hz₀, by rw [cm_zero]; exact left_mem_segment ℝ u (α z₀)⟩
    · refine ⟨α (‖z‖⁻¹ • z), hαA (mem_sphere_zero_iff_norm.mpr (norm_normalize hz0)), ?_⟩
      rw [segment_eq_image']
      exact ⟨‖z‖, ⟨norm_nonneg _, mem_closedBall_zero_iff.mp hz⟩, rfl⟩
  · rintro ⟨a, haA, hx⟩
    obtain ⟨z₁, hz₁, rfl⟩ := hαonto a haA
    rw [segment_eq_image'] at hx
    obtain ⟨θ, ⟨h0, h1⟩, rfl⟩ := hx
    rcases eq_or_lt_of_le h0 with rfl | hθ
    · exact ⟨0, mem_closedBall_self zero_le_one, by simp [cm_zero]⟩
    · have hz1 := mem_sphere_zero_iff_norm.mp hz₁
      refine ⟨θ • z₁, ?_, cm_smul α u hz1 hθ⟩
      rw [mem_closedBall_zero_iff, norm_smul, hz1, mul_one, Real.norm_of_nonneg hθ.le]
      exact h1

end cone

end Sol_Plasticity_Faces_reflected_preimage_eq_cone

open Set Metric Topology Sol_Plasticity_Faces_reflected_preimage_eq_cone Plasticity in
theorem solution {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (F : X → Y)
    (hbij : Set.BijOn F (Metric.closedBall (0 : X) 1) (Metric.closedBall (0 : Y) 1))
    (hlip : LipschitzOnWith 1 F (Metric.closedBall (0 : X) 1))
    (C : Set Y) (hC : IsSphereFace C) (hn : 1 ≤ Module.finrank ℝ (vectorSpan ℝ C))
    (hAc : IsCompact (Metric.closedBall (0 : X) 1 ∩ F ⁻¹' intrinsicFrontier ℝ C))
    (hAe : IsExtreme ℝ (Metric.closedBall (0 : X) 1)
      (Metric.closedBall (0 : X) 1 ∩ F ⁻¹' intrinsicFrontier ℝ C))
    (hAs : ∀ x ∈ Metric.closedBall (0 : X) 1,
      F x ∈ intrinsicFrontier ℝ C ↔ -F (-x) ∈ intrinsicFrontier ℝ C) :
    IsCompact {x | x ∈ Metric.closedBall (0 : X) 1 ∧ -F (-x) ∈ C} ∧
    ∀ u ∈ Metric.closedBall (0 : X) 1, F u ∈ C → F u ∉ intrinsicFrontier ℝ C →
      ∀ x, (x ∈ Metric.closedBall (0 : X) 1 ∧ -F (-x) ∈ C) ↔
        ∃ a ∈ Metric.closedBall (0 : X) 1 ∩ F ⁻¹' intrinsicFrontier ℝ C,
          x ∈ segment ℝ u a := by
  obtain ⟨hCne, hCconv, hCsph, hCext⟩ := hC
  -- `finrank` is `0` on infinite-dimensional spaces, so `hn` gives finite dimension
  have hfin : FiniteDimensional ℝ (vectorSpan ℝ C) := Module.finite_of_finrank_pos (by omega)
  have hfin' := hfin
  obtain ⟨hCcpt, -⟩ := Plasticity.Faces.isCompact_and_eq_closedBall_inter_affineSpan C ⟨hCne, hCconv, hCsph, hCext⟩ hfin
  have hCcl : IsClosed C := hCcpt.isClosed
  have hbdC : intrinsicFrontier ℝ C ⊆ C := intrinsicFrontier_subset hCcl
  have hCB : C ⊆ closedBall (0 : Y) 1 := hCext.subset
  obtain ⟨hF0, hFnorm, -, -, -⟩ := Sol_Plasticity_Faces_reflected_preimage_eq_cone.ballMap_facts F hbij hlip
  have hFcont : ContinuousOn F (closedBall (0 : X) 1) := hlip.continuousOn
  set A := closedBall (0 : X) 1 ∩ F ⁻¹' intrinsicFrontier ℝ C with hA
  -- the reflected map `Ft x = -F (-x)`
  set Ft : X → Y := fun x => -F (-x) with hFt
  have hnegB : ∀ x ∈ closedBall (0 : X) 1, -x ∈ closedBall (0 : X) 1 :=
    fun x hx => by simpa using hx
  have hFtcont : ContinuousOn Ft (closedBall (0 : X) 1) :=
    (hFcont.comp continuous_neg.continuousOn hnegB).neg
  have hFtB : ∀ x ∈ closedBall (0 : X) 1, Ft x ∈ closedBall (0 : Y) 1 := by
    intro x hx
    simpa [Ft] using hbij.mapsTo (hnegB x hx)
  have hFtinj : InjOn Ft (closedBall (0 : X) 1) := by
    intro x hx y hy h
    exact neg_injective (hbij.injOn (hnegB x hx) (hnegB y hy) (neg_injective h))
  have hFtsurj : ∀ y ∈ closedBall (0 : Y) 1, ∃ x ∈ closedBall (0 : X) 1, Ft x = y := by
    intro y hy
    obtain ⟨x, hx, hxy⟩ := hbij.surjOn (show -y ∈ closedBall (0 : Y) 1 by simpa using hy)
    exact ⟨-x, hnegB x hx, by simp [Ft, hxy]⟩
  set Gt : Y → X := Function.invFunOn Ft (closedBall (0 : X) 1) with hGt
  have hGt1 : ∀ y ∈ closedBall (0 : Y) 1, Gt y ∈ closedBall (0 : X) 1 ∧ Ft (Gt y) = y :=
    fun y hy => ⟨Function.invFunOn_mem (hFtsurj y hy), Function.invFunOn_eq (hFtsurj y hy)⟩
  have hGt2 : ∀ x ∈ closedBall (0 : X) 1, Gt (Ft x) = x := fun x hx =>
    hFtinj (hGt1 _ (hFtB x hx)).1 hx (hGt1 _ (hFtB x hx)).2
  -- facts about `A`
  have hA_Ft : ∀ a ∈ A, Ft a ∈ intrinsicFrontier ℝ C := fun a ha => (hAs a ha.1).mp ha.2
  have hFt_A : ∀ x ∈ closedBall (0 : X) 1, Ft x ∈ intrinsicFrontier ℝ C → x ∈ A :=
    fun x hx h => ⟨hx, (hAs x hx).mpr h⟩
  have hH : ∀ p ∈ closedBall (0 : X) 1, ∀ q ∈ closedBall (0 : X) 1, ∀ μ ∈ Ioo (0 : ℝ) 1,
      p + μ • (q - p) ∈ A → p ∈ A := by
    intro p hp q hq μ hμ hx
    exact hAe.left_mem_of_mem_openSegment hp hq hx
      (by rw [openSegment_eq_image']; exact ⟨μ, hμ, rfl⟩)
  -- the ball model of `C`
  obtain ⟨φ, ψ, hφc, hψc, hφ, hψ⟩ :=
    Plasticity.Topology.exists_closedBall_model_of_convex_compact C hCcpt hCconv hCne hfin
  have hpos : 0 < Module.finrank ℝ (vectorSpan ℝ C) := by omega
  have hVnt : Nontrivial (vectorSpan ℝ C) := Module.nontrivial_of_finrank_pos hpos
  have hsph_ne : (sphere (0 : vectorSpan ℝ C) 1).Nonempty :=
    NormedSpace.sphere_nonempty.mpr zero_le_one
  have hφsph : ∀ z : vectorSpan ℝ C, z ∈ sphere (0 : vectorSpan ℝ C) 1 →
      φ z ∈ intrinsicFrontier ℝ C := by
    intro z hz
    have hz1 := mem_sphere_zero_iff_norm.mp hz
    exact (hφ z hz1.le).2.2.mpr hz1
  -- `Gt` is continuous on the relative boundary
  have hFtA : Ft '' A = intrinsicFrontier ℝ C := by
    apply Subset.antisymm
    · rintro _ ⟨a, ha, rfl⟩
      exact hA_Ft a ha
    · intro y hy
      obtain ⟨h1, h2⟩ := hGt1 y (hCB (hbdC hy))
      exact ⟨Gt y, hFt_A _ h1 (by rw [h2]; exact hy), h2⟩
  have hGtbd : ContinuousOn Gt (intrinsicFrontier ℝ C) :=
    hFtA ▸ contOn_leftInv hAc (hFtcont.mono inter_subset_left) (fun x hx => hGt2 x hx.1)
  -- the parametrization `α` of `A` by the unit sphere of `vectorSpan ℝ C`
  set α : vectorSpan ℝ C → X := fun z => Gt (φ z) with hα
  have hαc : ContinuousOn α (sphere (0 : vectorSpan ℝ C) 1) :=
    hGtbd.comp hφc.continuousOn hφsph
  have hαA : MapsTo α (sphere (0 : vectorSpan ℝ C) 1) A := by
    intro z hz
    obtain ⟨h1, h2⟩ := hGt1 (φ z) (hCB (hbdC (hφsph z hz)))
    exact hFt_A _ h1 (h2.symm ▸ hφsph z hz)
  have hαB : ∀ z ∈ sphere (0 : vectorSpan ℝ C) 1, ‖α z‖ ≤ 1 :=
    fun z hz => mem_closedBall_zero_iff.mp (hαA hz).1
  have hαinj : InjOn α (sphere (0 : vectorSpan ℝ C) 1) := by
    intro z₁ hz₁ z₂ hz₂ h
    have h1 : φ z₁ = φ z₂ := by
      rw [← (hGt1 (φ z₁) (hCB (hbdC (hφsph z₁ hz₁)))).2,
        ← (hGt1 (φ z₂) (hCB (hbdC (hφsph z₂ hz₂)))).2]
      exact congrArg Ft h
    rw [← (hφ z₁ (mem_sphere_zero_iff_norm.mp hz₁).le).2.1,
      ← (hφ z₂ (mem_sphere_zero_iff_norm.mp hz₂).le).2.1, h1]
  have hαonto : ∀ a ∈ A, ∃ z ∈ sphere (0 : vectorSpan ℝ C) 1, α z = a := by
    intro a ha
    have hFta := hA_Ft a ha
    obtain ⟨hψ1, hψ2⟩ := hψ (Ft a) (hbdC hFta)
    have hz1 : ‖ψ (Ft a)‖ = 1 := (hφ _ hψ1).2.2.mp (hψ2.symm ▸ hFta)
    refine ⟨ψ (Ft a), mem_sphere_zero_iff_norm.mpr hz1, ?_⟩
    simp only [α]
    rw [hψ2, hGt2 a ha.1]
  -- the projection onto `vectorSpan ℝ C`
  obtain ⟨P, hP⟩ := Submodule.ClosedComplemented.of_finiteDimensional (vectorSpan ℝ C)
  -- the argument for one apex `u`
  have key : ∀ u ∈ closedBall (0 : X) 1, F u ∈ C → F u ∉ intrinsicFrontier ℝ C →
      (∀ x ∈ closedBall (0 : X) 1, Ft x ∈ C → ∃ a ∈ A, x ∈ segment ℝ u a) ∧
      (IsCompact {x | x ∈ closedBall (0 : X) 1 ∧ -F (-x) ∈ C} →
        ∀ x, (∃ a ∈ A, x ∈ segment ℝ u a) → x ∈ closedBall (0 : X) 1 ∧ Ft x ∈ C) := by
    intro u hu hFuC hFuA
    have huA : u ∉ A := fun h => hFuA h.2
    have hnotA : ∀ a ∈ A, ∀ l ∈ Ico (0 : ℝ) 1, u + l • (a - u) ∉ A := by
      intro a ha l hl hmem
      rcases eq_or_lt_of_le hl.1 with h0 | hpos
      · rw [← h0, zero_smul, add_zero] at hmem
        exact huA hmem
      · exact huA (hH u hu a ha.1 l ⟨hpos, hl.2⟩ hmem)
    have hu1 : ‖u‖ ≤ 1 := mem_closedBall_zero_iff.mp hu
    set Q := cm α u with hQ
    have hQc : ContinuousOn Q (closedBall 0 1) := cm_cont α hαc hαB hu1
    have hQinj : InjOn Q (closedBall 0 1) := cm_inj α hαA hαinj hnotA
    have hQimg : Q '' closedBall 0 1 = {x | ∃ a ∈ A, x ∈ segment ℝ u a} :=
      cm_image α u hαA hαonto hsph_ne
    have hQB : ∀ z : vectorSpan ℝ C, ‖z‖ ≤ 1 → Q z ∈ closedBall (0 : X) 1 :=
      fun z hz => mem_closedBall_zero_iff.mpr (cm_norm α hαB hu1 hz)
    -- Step 2: a neighbourhood of `0` in `vectorSpan ℝ C`
    have hwB : ∀ z : vectorSpan ℝ C, ‖z‖ ≤ 1 →
        (1 / 4 : ℝ) • (u - Q z) ∈ closedBall (0 : X) 1 := by
      intro z hz
      have h1 := mem_closedBall_zero_iff.mp (hQB z hz)
      rw [mem_closedBall_zero_iff, norm_smul, Real.norm_of_nonneg (by norm_num)]
      have h2 : ‖u - Q z‖ ≤ 2 := (norm_sub_le _ _).trans (by linarith)
      linarith
    have hFwV : ∀ z : vectorSpan ℝ C, ‖z‖ ≤ 1 →
        F ((1 / 4 : ℝ) • (u - Q z)) ∈ vectorSpan ℝ C := by
      intro z hz
      rw [hQ, cm_sub]
      rcases eq_or_ne z 0 with rfl | hz0
      · simp [hF0]
      · have hs := mem_sphere_zero_iff_norm.mpr (norm_normalize hz0)
        exact two_balls_t F hlip hCconv hCext hu hFuC (hαA hs).1
          (hbdC (hA_Ft _ (hαA hs))) (by positivity) (by linarith)
    let Ψ : vectorSpan ℝ C → vectorSpan ℝ C := fun z => P (F ((1 / 4 : ℝ) • (u - Q z)))
    have hΨval : ∀ z : vectorSpan ℝ C, ‖z‖ ≤ 1 →
        (Ψ z : Y) = F ((1 / 4 : ℝ) • (u - Q z)) := by
      intro z hz
      have h1 := hP ⟨_, hFwV z hz⟩
      simp only [Ψ]
      rw [h1]
    have hΨc : ContinuousOn Ψ (ball 0 1) := by
      apply P.continuous.comp_continuousOn
      refine hFcont.comp ?_ (fun z hz => hwB z (mem_ball_zero_iff.mp hz).le)
      exact continuousOn_const.smul (continuousOn_const.sub (hQc.mono ball_subset_closedBall))
    have hΨinj : InjOn Ψ (ball 0 1) := by
      intro z₁ hz₁ z₂ hz₂ h
      have h1 := mem_ball_zero_iff.mp hz₁
      have h2 := mem_ball_zero_iff.mp hz₂
      have h3 : (Ψ z₁ : Y) = Ψ z₂ := by rw [h]
      rw [hΨval z₁ h1.le, hΨval z₂ h2.le] at h3
      have h4 := hbij.injOn (hwB z₁ h1.le) (hwB z₂ h2.le) h3
      have h5 : Q z₁ = Q z₂ := by
        have h6 := smul_right_injective X (by norm_num : (1 / 4 : ℝ) ≠ 0) h4
        simpa using h6
      exact hQinj (ball_subset_closedBall hz₁) (ball_subset_closedBall hz₂) h5
    have hopen := Plasticity.Topology.isOpen_image_of_injOn_of_finrank_eq rfl (ball 0 1) isOpen_ball Ψ hΨc hΨinj
    have hΨ0 : Ψ 0 = 0 := by
      apply Subtype.ext
      rw [hΨval 0 (by simp), hQ, cm_zero, sub_self, smul_zero, hF0]
      rfl
    obtain ⟨ε, hε, hεsub⟩ := Metric.isOpen_iff.mp hopen 0 ⟨0, mem_ball_self one_pos, hΨ0⟩
    -- Step 3: the reflected preimage lies in the cone `Q_u`
    have step3 : ∀ x ∈ closedBall (0 : X) 1, Ft x ∈ C → ∃ a ∈ A, x ∈ segment ℝ u a := by
      intro v hv hFtv
      by_cases hvA : v ∈ A
      · exact ⟨v, hvA, right_mem_segment ℝ u v⟩
      by_cases hvu : v = u
      · obtain ⟨z, hz⟩ := hsph_ne
        exact ⟨α z, hαA hz, hvu ▸ left_mem_segment ℝ u (α z)⟩
      set t : ℝ := min (1 / 4) (ε / 4) with ht
      have ht0 : 0 < t := lt_min (by norm_num) (by linarith)
      have ht14 : t ≤ 1 / 4 := min_le_left _ _
      have htε : t ≤ ε / 4 := min_le_right _ _
      have hyV : F (t • (u - v)) ∈ vectorSpan ℝ C :=
        two_balls_t F hlip hCconv hCext hu hFuC hv hFtv ht0.le ht14
      have hv1 := mem_closedBall_zero_iff.mp hv
      have huv : ‖u - v‖ ≤ 2 := (norm_sub_le _ _).trans (by linarith)
      have hnw : ‖t • (u - v)‖ ≤ t * 2 := by
        rw [norm_smul, Real.norm_of_nonneg ht0.le]
        exact mul_le_mul_of_nonneg_left huv ht0.le
      have htwB : t • (u - v) ∈ closedBall (0 : X) 1 := by
        rw [mem_closedBall_zero_iff]
        linarith
      have hynorm : ‖F (t • (u - v))‖ < ε := by
        have := hFnorm _ htwB
        linarith
      obtain ⟨z, hz, hΨz⟩ := hεsub (show (⟨_, hyV⟩ : vectorSpan ℝ C) ∈ ball 0 ε by
        rw [mem_ball_zero_iff]
        exact hynorm)
      have hz1 : ‖z‖ ≤ 1 := (mem_ball_zero_iff.mp hz).le
      have heq : (1 / 4 : ℝ) • (u - Q z) = t • (u - v) := by
        have h1 : (Ψ z : Y) = F (t • (u - v)) := by rw [hΨz]
        rw [hΨval z hz1] at h1
        exact hbij.injOn (hwB z hz1) htwB h1
      rw [hQ, cm_sub] at heq
      have hz0 : z ≠ 0 := by
        rintro rfl
        simp only [norm_zero, zero_div, zero_smul] at heq
        rcases smul_eq_zero.mp heq.symm with h | h
        · exact ht0.ne' h
        · exact hvu (sub_eq_zero.mp h).symm
      have hs := mem_sphere_zero_iff_norm.mpr (norm_normalize hz0)
      set a := α (‖z‖⁻¹ • z) with ha
      have haA : a ∈ A := hαA hs
      have hs0 : 0 < ‖z‖ := norm_pos_iff.mpr hz0
      set l := ‖z‖ / (4 * t) with hl
      have hl0 : 0 < l := by positivity
      have hv_eq : v = u + l • (a - u) := by
        have h1 : v - u = l • (a - u) := by
          have h2 : t • (v - u) = (‖z‖ / 4) • (a - u) := by
            have h3 : t • (v - u) = -(t • (u - v)) := by rw [← smul_neg, neg_sub]
            rw [h3, ← heq, ← smul_neg, neg_sub]
          have h4 : v - u = t⁻¹ • ((‖z‖ / 4) • (a - u)) := by
            rw [← h2, smul_smul, inv_mul_cancel₀ ht0.ne', one_smul]
          rw [h4, smul_smul]
          congr 1
          rw [hl]
          field_simp
        rw [← h1]
        abel
      by_cases hl1 : l ≤ 1
      · refine ⟨a, haA, ?_⟩
        rw [segment_eq_image']
        exact ⟨l, ⟨hl0.le, hl1⟩, hv_eq.symm⟩
      · exfalso
        push Not at hl1
        have ha_eq : a = u + l⁻¹ • (v - u) := by
          rw [hv_eq, add_sub_cancel_left, smul_smul, inv_mul_cancel₀ hl0.ne', one_smul]
          abel
        exact huA (hH u hu v hv l⁻¹ ⟨inv_pos.mpr hl0, inv_lt_one_of_one_lt₀ hl1⟩
          (ha_eq ▸ haA))
    refine ⟨step3, fun hD'c x hx => ?_⟩
    -- Step 4: the cone `Q_u` lies in the reflected preimage
    have hFtD' : Ft '' {x | x ∈ closedBall (0 : X) 1 ∧ -F (-x) ∈ C} = C := by
      apply Subset.antisymm
      · rintro _ ⟨y, hy, rfl⟩
        exact hy.2
      · intro y hy
        obtain ⟨h1, h2⟩ := hGt1 y (hCB hy)
        exact ⟨Gt y, ⟨h1, by simpa [Ft] using (h2.symm ▸ hy : Ft (Gt y) ∈ C)⟩, h2⟩
    have hGtc : ContinuousOn Gt C :=
      hFtD' ▸ contOn_leftInv hD'c (hFtcont.mono (fun x hx => hx.1)) (fun x hx => hGt2 x hx.1)
    let β : vectorSpan ℝ C → X := fun z => Gt (φ z)
    have hβc : ContinuousOn β (closedBall 0 1) :=
      hGtc.comp hφc.continuousOn (fun z hz => (hφ z (mem_closedBall_zero_iff.mp hz)).1)
    have hβD' : ∀ z : vectorSpan ℝ C, ‖z‖ ≤ 1 →
        β z ∈ closedBall (0 : X) 1 ∧ Ft (β z) ∈ C := by
      intro z hz
      obtain ⟨h1, h2⟩ := hGt1 (φ z) (hCB (hφ z hz).1)
      exact ⟨h1, h2.symm ▸ (hφ z hz).1⟩
    have hβQ : ∀ z : vectorSpan ℝ C, ‖z‖ ≤ 1 → β z ∈ Q '' closedBall 0 1 := by
      intro z hz
      rw [hQimg]
      exact step3 _ (hβD' z hz).1 (hβD' z hz).2
    set Qi := Function.invFunOn Q (closedBall (0 : vectorSpan ℝ C) 1) with hQi
    have hQiQ : ∀ z ∈ closedBall (0 : vectorSpan ℝ C) 1, Qi (Q z) = z :=
      fun z hz => hQinj.leftInvOn_invFunOn hz
    have hQic : ContinuousOn Qi (Q '' closedBall 0 1) :=
      contOn_leftInv (isCompact_closedBall 0 1) hQc hQiQ
    let g : vectorSpan ℝ C → vectorSpan ℝ C := fun z => Qi (β z)
    have hgc : ContinuousOn g (closedBall 0 1) :=
      hQic.comp hβc (fun z hz => hβQ z (mem_closedBall_zero_iff.mp hz))
    have hgid : ∀ z ∈ sphere (0 : vectorSpan ℝ C) 1, g z = z := by
      intro z hz
      have h1 : β z = Q z := by
        rw [hQ, cm_sphere α u (mem_sphere_zero_iff_norm.mp hz)]
      simp only [g]
      rw [h1]
      exact hQiQ z (sphere_subset_closedBall hz)
    have honto := Plasticity.Topology.closedBall_subset_image_of_eqOn_sphere g hgc hgid
    have hxQ : x ∈ Q '' closedBall 0 1 := by
      rw [hQimg]
      exact hx
    obtain ⟨z, hz, rfl⟩ := hxQ
    obtain ⟨z', hz', hgz'⟩ := honto hz
    have h1 : Q z = β z' := by
      rw [← hgz']
      exact Function.invFunOn_eq (hβQ z' (mem_closedBall_zero_iff.mp hz'))
    rw [h1]
    exact hβD' z' (mem_closedBall_zero_iff.mp hz')
  -- an apex `u₀` and the compactness of the reflected preimage
  have hφ0 := hφ 0 (by simp)
  obtain ⟨u₀, hu₀B, hu₀⟩ := hbij.surjOn (hCB hφ0.1)
  have hFu₀C : F u₀ ∈ C := hu₀ ▸ hφ0.1
  have hFu₀A : F u₀ ∉ intrinsicFrontier ℝ C := by
    rw [hu₀]
    intro h
    have h1 := hφ0.2.2.mp h
    simp at h1
  have step3₀ := (key u₀ hu₀B hFu₀C hFu₀A).1
  have hD'cl : IsClosed {x | x ∈ closedBall (0 : X) 1 ∧ -F (-x) ∈ C} :=
    hFtcont.preimage_isClosed_of_isClosed isClosed_closedBall hCcl
  have hKc : IsCompact ((fun p : ℝ × X => u₀ + p.1 • (p.2 - u₀)) '' (Icc (0 : ℝ) 1 ×ˢ A)) :=
    (isCompact_Icc.prod hAc).image (by fun_prop)
  have hD'c : IsCompact {x | x ∈ closedBall (0 : X) 1 ∧ -F (-x) ∈ C} := by
    refine hKc.of_isClosed_subset hD'cl ?_
    intro x hx
    obtain ⟨a, haA, hxa⟩ := step3₀ x hx.1 hx.2
    rw [segment_eq_image'] at hxa
    obtain ⟨θ, hθ, rfl⟩ := hxa
    exact ⟨(θ, a), ⟨hθ, haA⟩, rfl⟩
  refine ⟨hD'c, fun u hu hFu hFuA x => ⟨fun hx => (key u hu hFu hFuA).1 x hx.1 hx.2,
    fun hx => (key u hu hFu hFuA).2 hD'c x hx⟩⟩
