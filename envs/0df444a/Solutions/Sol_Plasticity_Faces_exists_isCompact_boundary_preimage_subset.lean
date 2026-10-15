-- Prove2me | solution 1 for Plasticity.Faces.exists_isCompact_boundary_preimage_subset
-- status  : ACCEPTED   (prove)
-- author  : @scanstone
-- created : 2026-10-15T00:38:58.740327+00:00
-- url     : https://prove2.me/submissions/9758cb93-55a7-40ba-b6ab-aa2fa541403a

/-
The lemmas `homeo_interior_nonempty` and `ri_nonempty` below adapt the proof of
`Set.Nonempty.intrinsicInterior` and its private helper `aux` from Mathlib
(Mathlib/Analysis/Convex/Intrinsic.lean, https://github.com/leanprover-community/mathlib4,
Apache License 2.0), replacing finite-dimensionality of the ambient space by that of the
direction of the affine span.
-/
import Theorems.Thm_Plasticity_BallMap_map_zero_of_surjOn
import Theorems.Thm_Plasticity_BallMap_norm_map_le
import Theorems.Thm_Plasticity_BallMap_mem_sphere_of_map_mem_sphere
import Theorems.Thm_Plasticity_BallMap_norm_map_eq_of_mapsTo_sphere
import Theorems.Thm_Plasticity_BallMap_map_neg_of_map_mem_extremePoints
import Theorems.Thm_Plasticity_BallMap_mem_extremePoints_of_map_mem_extremePoints
import Theorems.Thm_Plasticity_BallMap_map_smul_of_map_mem_extremePoints
import Theorems.Thm_Plasticity_Faces_exists_common_face_of_preimages
import Theorems.Thm_Plasticity_Aux_exists_proper_face
import Theorems.Thm_Plasticity_Faces_isCompact_and_eq_closedBall_inter_affineSpan
import Mathlib.Analysis.Convex.Intrinsic
import Mathlib.Analysis.Normed.Affine.AddTorsorBases
import Mathlib.Topology.Connected.Clopen
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Tactic.Module

namespace Sol_Plasticity_Faces_exists_isCompact_boundary_preimage_subset

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

end Sol_Plasticity_Faces_exists_isCompact_boundary_preimage_subset


open Plasticity
open scoped Pointwise

namespace Sol_Plasticity_Faces_exists_isCompact_boundary_preimage_subset

open Set Metric

/-- A `1`-Lipschitz map on `s`, stated with norms. -/
lemma lip_norm {X Y : Type*} [NormedAddCommGroup X] [NormedAddCommGroup Y] {F : X → Y}
    {s : Set X} (hlip : LipschitzOnWith 1 F s) {x y : X} (hx : x ∈ s) (hy : y ∈ s) :
    ‖F x - F y‖ ≤ ‖x - y‖ := by
  have h := hlip.dist_le_mul x hx y hy
  simpa [dist_eq_norm] using h

/-- Radial entry (1.3): if `f x` lies in an extreme subset `S` of the ball, then `f (t x) ∈ t S`. -/
lemma radial {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] (f : X → Y) (h0 : f 0 = 0)
    (hf : ∀ x ∈ closedBall (0 : X) 1, ∀ y ∈ closedBall (0 : X) 1, ‖f x - f y‖ ≤ ‖x - y‖)
    (S : Set Y) (hS : IsExtreme ℝ (closedBall (0 : Y) 1) S) (hSne : S.Nonempty)
    (x : X) (hx : x ∈ closedBall (0 : X) 1) (hfx : f x ∈ S) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    ∃ e ∈ S, f (t • x) = t • e := by
  rcases eq_or_lt_of_le ht0 with rfl | ht0'
  · obtain ⟨e, he⟩ := hSne
    exact ⟨e, he, by simp [h0]⟩
  rcases eq_or_lt_of_le ht1 with rfl | ht1'
  · exact ⟨f x, hfx, by simp⟩
  have hx1 : ‖x‖ ≤ 1 := by simpa using hx
  have h1t : 0 < 1 - t := by linarith
  have htx : t • x ∈ closedBall (0 : X) 1 := by
    rw [mem_closedBall_zero_iff, norm_smul, Real.norm_of_nonneg ht0]
    nlinarith [norm_nonneg x]
  have hB0 : (0 : X) ∈ closedBall (0 : X) 1 := by simp
  set p₁ : Y := t⁻¹ • f (t • x) with hp₁def
  set p₂ : Y := (1 - t)⁻¹ • (f x - f (t • x)) with hp₂def
  have hp₁ : p₁ ∈ closedBall (0 : Y) 1 := by
    rw [mem_closedBall_zero_iff, hp₁def, norm_smul, Real.norm_of_nonneg (inv_nonneg.2 ht0)]
    have h := hf _ htx 0 hB0
    rw [h0, sub_zero, sub_zero, norm_smul, Real.norm_of_nonneg ht0] at h
    rw [inv_mul_le_iff₀ ht0', mul_one]
    nlinarith [norm_nonneg x]
  have hp₂ : p₂ ∈ closedBall (0 : Y) 1 := by
    rw [mem_closedBall_zero_iff, hp₂def, norm_smul, Real.norm_of_nonneg (inv_nonneg.2 h1t.le)]
    have h := hf _ hx _ htx
    rw [show x - t • x = (1 - t) • x by rw [sub_smul, one_smul], norm_smul,
      Real.norm_of_nonneg h1t.le] at h
    rw [inv_mul_le_iff₀ h1t, mul_one]
    nlinarith [norm_nonneg x]
  have hseg : f x ∈ openSegment ℝ p₁ p₂ := by
    refine ⟨t, 1 - t, ht0', h1t, by ring, ?_⟩
    rw [hp₁def, hp₂def, smul_smul, smul_smul, mul_inv_cancel₀ ht0'.ne',
      mul_inv_cancel₀ h1t.ne', one_smul, one_smul]
    abel
  refine ⟨p₁, hS.left_mem_of_mem_openSegment hp₁ hp₂ hfx hseg, ?_⟩
  rw [hp₁def, smul_smul, mul_inv_cancel₀ ht0'.ne', one_smul]

/-- Mixed sectors (Lemma 4): `F (u q - v a) = (u + v) e - 2 v c` with `e, c ∈ C`. -/
lemma mixed {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] (F : X → Y) (h0 : F 0 = 0)
    (hF : ∀ x ∈ closedBall (0 : X) 1, ∀ y ∈ closedBall (0 : X) 1, ‖F x - F y‖ ≤ ‖x - y‖)
    (C : Set Y) (hext : IsExtreme ℝ (closedBall (0 : Y) 1) C) (hconv : Convex ℝ C)
    (hne : C.Nonempty) (q a : X) (hq : q ∈ closedBall (0 : X) 1) (ha : a ∈ closedBall (0 : X) 1)
    (hFq : F q ∈ C) (hFa : -F (-a) ∈ C) (u v : ℝ) (hu : 0 < u) (hv : 0 < v) (huv : u + v ≤ 1) :
    ∃ e ∈ C, ∃ c ∈ C, F (u • q - v • a) = (u + v) • e - (2 * v) • c := by
  have hq1 : ‖q‖ ≤ 1 := by simpa using hq
  have ha1 : ‖a‖ ≤ 1 := by simpa using ha
  have hs0 : 0 < u + v := by linarith
  obtain ⟨e, heC, he⟩ := radial F h0 hF C hext hne q hq hFq (u + v) hs0.le huv
  have hF' : ∀ x ∈ closedBall (0 : X) 1, ∀ y ∈ closedBall (0 : X) 1,
      ‖(fun z => -F (-z)) x - (fun z => -F (-z)) y‖ ≤ ‖x - y‖ := by
    intro x hx y hy
    have := hF (-y) (by simpa using hy) (-x) (by simpa using hx)
    rw [show -y - -x = x - y by abel] at this
    rw [show -F (-x) - -F (-y) = F (-y) - F (-x) by abel]
    exact this
  obtain ⟨f, hfC, hf⟩ :=
    radial (fun z => -F (-z)) (by simp [h0]) hF' C hext hne a ha hFa (u + v) hs0.le huv
  have hxB : u • q - v • a ∈ closedBall (0 : X) 1 := by
    rw [mem_closedBall_zero_iff]
    calc ‖u • q - v • a‖ ≤ ‖u • q‖ + ‖v • a‖ := norm_sub_le _ _
      _ = u * ‖q‖ + v * ‖a‖ := by
        rw [norm_smul, norm_smul, Real.norm_of_nonneg hu.le, Real.norm_of_nonneg hv.le]
      _ ≤ u + v := by nlinarith
      _ ≤ 1 := huv
  have hsqB : (u + v) • q ∈ closedBall (0 : X) 1 := by
    rw [mem_closedBall_zero_iff, norm_smul, Real.norm_of_nonneg hs0.le]
    nlinarith [norm_nonneg q]
  have hsaB : -((u + v) • a) ∈ closedBall (0 : X) 1 := by
    rw [mem_closedBall_zero_iff, norm_neg, norm_smul, Real.norm_of_nonneg hs0.le]
    nlinarith [norm_nonneg a]
  have hqa2 : ‖q + a‖ ≤ 2 := by linarith [norm_add_le q a]
  have h1 : ‖(u + v) • e - F (u • q - v • a)‖ ≤ 2 * v := by
    rw [← he]
    calc ‖F ((u + v) • q) - F (u • q - v • a)‖ ≤ ‖(u + v) • q - (u • q - v • a)‖ :=
          hF _ hsqB _ hxB
      _ = ‖v • (q + a)‖ := by congr 1; module
      _ = v * ‖q + a‖ := by rw [norm_smul, Real.norm_of_nonneg hv.le]
      _ ≤ 2 * v := by nlinarith
  have h2 : ‖F (u • q - v • a) + (u + v) • f‖ ≤ 2 * u := by
    rw [← hf]
    calc ‖F (u • q - v • a) + -F (-((u + v) • a))‖
        = ‖F (u • q - v • a) - F (-((u + v) • a))‖ := by rw [sub_eq_add_neg (F (u • q - v • a))]
      _ ≤ ‖(u • q - v • a) - -((u + v) • a)‖ := hF _ hxB _ hsaB
      _ = ‖u • (q + a)‖ := by congr 1; module
      _ = u * ‖q + a‖ := by rw [norm_smul, Real.norm_of_nonneg hu.le]
      _ ≤ 2 * u := by nlinarith
  set p₁ : Y := (2 * v)⁻¹ • ((u + v) • e - F (u • q - v • a)) with hp₁def
  set p₂ : Y := (2 * u)⁻¹ • (F (u • q - v • a) + (u + v) • f) with hp₂def
  have hp₁ : p₁ ∈ closedBall (0 : Y) 1 := by
    rw [mem_closedBall_zero_iff, hp₁def, norm_smul, Real.norm_of_nonneg (by positivity),
      inv_mul_le_iff₀ (by positivity), mul_one]
    exact h1
  have hp₂ : p₂ ∈ closedBall (0 : Y) 1 := by
    rw [mem_closedBall_zero_iff, hp₂def, norm_smul, Real.norm_of_nonneg (by positivity),
      inv_mul_le_iff₀ (by positivity), mul_one]
    exact h2
  have hmid : (1 / 2 : ℝ) • e + (1 / 2 : ℝ) • f ∈ C :=
    hconv heC hfC (by norm_num) (by norm_num) (by norm_num)
  have hv0 : v ≠ 0 := hv.ne'
  have hu0 : u ≠ 0 := hu.ne'
  have hs0' : u + v ≠ 0 := hs0.ne'
  have hseg : (1 / 2 : ℝ) • e + (1 / 2 : ℝ) • f ∈ openSegment ℝ p₁ p₂ := by
    refine ⟨v / (u + v), u / (u + v), by positivity, by positivity, ?_, ?_⟩
    · rw [← add_div, add_comm, div_self hs0']
    rw [hp₁def, hp₂def]
    match_scalars <;> field_simp <;> ring
  have hp₁C := hext.left_mem_of_mem_openSegment hp₁ hp₂ hmid hseg
  refine ⟨e, heC, p₁, hp₁C, ?_⟩
  rw [hp₁def, smul_smul, mul_inv_cancel₀ (by positivity : (2 * v) ≠ 0), one_smul]
  abel

/-- A relative-interior point `c₀` of `C` can be pushed slightly beyond itself away from any
`z ∈ C`. -/
lemma core {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y] (C : Set Y) (c₀ : Y)
    (hc₀ : c₀ ∈ intrinsicInterior ℝ C) (z : Y) (hz : z ∈ C) :
    ∃ ε : ℝ, 0 < ε ∧ c₀ + ε • (c₀ - z) ∈ C := by
  obtain ⟨p, hp, rfl⟩ := mem_intrinsicInterior.mp hc₀
  have hzA : z ∈ affineSpan ℝ C := subset_affineSpan ℝ C hz
  have hmem : ∀ ε : ℝ, (p : Y) + ε • ((p : Y) - z) ∈ affineSpan ℝ C := by
    intro ε
    have hd : ε • ((p : Y) - z) ∈ (affineSpan ℝ C).direction :=
      Submodule.smul_mem _ _ (AffineSubspace.vsub_mem_direction p.2 hzA)
    have := AffineSubspace.vadd_mem_of_mem_direction hd p.2
    simpa [vadd_eq_add, add_comm] using this
  let g : ℝ → affineSpan ℝ C := fun ε => ⟨(p : Y) + ε • ((p : Y) - z), hmem ε⟩
  have hg : Continuous g := by
    apply Continuous.subtype_mk
    fun_prop
  have hg0 : g 0 = p := by ext; simp [g]
  have hnhds : g ⁻¹' interior ((↑) ⁻¹' C : Set (affineSpan ℝ C)) ∈ nhds (0 : ℝ) := by
    apply hg.continuousAt.preimage_mem_nhds
    rw [hg0]
    exact isOpen_interior.mem_nhds hp
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp hnhds
  refine ⟨δ / 2, by positivity, ?_⟩
  have hmemb : δ / 2 ∈ ball (0 : ℝ) δ := by
    rw [mem_ball, Real.dist_eq, sub_zero, abs_of_pos (by positivity)]
    linarith
  have h := interior_subset (s := ((↑) ⁻¹' C : Set (affineSpan ℝ C))) (hball hmemb)
  exact h

/-- Interiors and homeomorphisms (Mathlib's private `aux` in `Analysis/Convex/Intrinsic`). -/
lemma homeo_interior_nonempty {α β : Type*} [TopologicalSpace α] [TopologicalSpace β]
    (φ : α ≃ₜ β) (s : Set β) : (interior s).Nonempty ↔ (interior (φ ⁻¹' s)).Nonempty := by
  rw [← φ.image_symm, ← φ.symm.image_interior, image_nonempty]

/-- The relative interior of a nonempty convex set with finite-dimensional direction is
nonempty (Mathlib's proof, with the ambient finite-dimensionality replaced). -/
lemma ri_nonempty {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y] (s : Set Y)
    (hscv : Convex ℝ s) (hsne : s.Nonempty) (hfin : FiniteDimensional ℝ (vectorSpan ℝ s)) :
    (intrinsicInterior ℝ s).Nonempty := by
  have := hsne.coe_sort
  obtain ⟨p, hp⟩ := hsne
  let p' : _root_.affineSpan ℝ s := ⟨p, subset_affineSpan _ _ hp⟩
  have : FiniteDimensional ℝ (affineSpan ℝ s).direction := by
    rw [direction_affineSpan]; exact hfin
  rw [intrinsicInterior, image_nonempty,
    homeo_interior_nonempty (AffineIsometryEquiv.constVSub ℝ p').symm.toHomeomorph,
    Convex.interior_nonempty_iff_affineSpan_eq_top, AffineIsometryEquiv.coe_toHomeomorph, ←
    AffineIsometryEquiv.coe_toAffineEquiv, ← AffineSubspace.comap_span,
    affineSpan_coe_preimage_eq_top, AffineSubspace.comap_top]
  exact hscv.affine_preimage
    ((_root_.affineSpan ℝ s).subtype.comp
      (AffineIsometryEquiv.constVSub ℝ p').symm.toAffineEquiv.toAffineMap)

/-- A relative-interior point lies in no extreme subset of smaller dimension. -/
lemma not_mem_proper {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y] (C C' : Set Y)
    (c₀ : Y) (hc₀ : c₀ ∈ intrinsicInterior ℝ C) (hext : IsExtreme ℝ C C')
    (hlt : Module.finrank ℝ (vectorSpan ℝ C') < Module.finrank ℝ (vectorSpan ℝ C)) :
    c₀ ∉ C' := by
  intro hc₀'
  have hsub : C ⊆ C' := by
    intro z hz
    obtain ⟨ε, hε, hw⟩ := core C c₀ hc₀ z hz
    have hε1 : (1 + ε) ≠ 0 := by positivity
    have hseg : c₀ ∈ openSegment ℝ (c₀ + ε • (c₀ - z)) z := by
      refine ⟨1 / (1 + ε), ε / (1 + ε), by positivity, by positivity, by field_simp, ?_⟩
      match_scalars <;> field_simp <;> ring
    exact hext.right_mem_of_mem_openSegment hw hz hc₀' hseg
  have heq : C' = C := Subset.antisymm hext.subset hsub
  rw [heq] at hlt
  exact lt_irrefl _ hlt

/-- The boundary crossing (4.3)–(4.6). -/
lemma crossing {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] (F : X → Y) (h0 : F 0 = 0)
    (hF : ∀ x ∈ closedBall (0 : X) 1, ∀ y ∈ closedBall (0 : X) 1, ‖F x - F y‖ ≤ ‖x - y‖)
    (hFc : ContinuousOn F (closedBall (0 : X) 1))
    (hinj : InjOn F (closedBall (0 : X) 1))
    (C : Set Y) (hext : IsExtreme ℝ (closedBall (0 : Y) 1) C) (hconv : Convex ℝ C)
    (hne : C.Nonempty) (hsph : C ⊆ sphere (0 : Y) 1)
    (q a : X) (hq : q ∈ closedBall (0 : X) 1) (ha : a ∈ closedBall (0 : X) 1)
    (hFq : F q ∈ C) (hFa : -F (-a) ∈ C) (hqa : q ≠ a)
    (hcov : ∀ y ∈ intrinsicFrontier ℝ C, ∀ t : ℝ, 0 < t → t ≤ 1 →
      ∃ b ∈ closedBall (0 : X) 1, b ≠ q ∧ F (t • b) = t • y) :
    ∃ b ∈ closedBall (0 : X) 1, q ∈ openSegment ℝ a b := by
  have hB0 : (0 : X) ∈ closedBall (0 : X) 1 := by simp
  have hq1 : ‖q‖ ≤ 1 := by simpa using hq
  have ha1 : ‖a‖ ≤ 1 := by simpa using ha
  -- the scale `λ = ‖F ((q - a) / 4)‖ / 4` of (4.3)
  set w : X := (1 / 4 : ℝ) • (q - a) with hw
  have hw_le : ‖w‖ ≤ 1 / 2 := by
    rw [hw, norm_smul, Real.norm_of_nonneg (by norm_num)]
    have := norm_sub_le q a
    linarith
  have hwB : w ∈ closedBall (0 : X) 1 := by
    rw [mem_closedBall_zero_iff]; linarith
  set d : ℝ := ‖F w‖ with hd
  have hd_le : d ≤ 1 / 2 := by
    have h := hF w hwB 0 hB0
    rw [h0, sub_zero, sub_zero] at h
    linarith
  have hd_pos : 0 < d := by
    rw [hd, norm_pos_iff]
    intro hFw
    have hw0 : w = 0 := hinj hwB hB0 (by rw [hFw, h0])
    rw [hw, smul_eq_zero] at hw0
    rcases hw0 with h | h
    · norm_num at h
    · exact hqa (sub_eq_zero.mp h)
  set lam : ℝ := d / 4 with hlam
  have hlam0 : 0 < lam := by positivity
  have hlam1 : lam ≤ 1 / 8 := by linarith
  -- the source path `x v = (λ + v) q - v a` of (4.4) and its rescaled image `z v`
  set x : ℝ → X := fun v => (lam + v) • q - v • a with hxdef
  have hxB : ∀ v, 0 ≤ v → v ≤ 1 / 4 → x v ∈ closedBall (0 : X) 1 := by
    intro v hv0 hv1
    rw [mem_closedBall_zero_iff]
    calc ‖x v‖ ≤ ‖(lam + v) • q‖ + ‖v • a‖ := norm_sub_le _ _
      _ = (lam + v) * ‖q‖ + v * ‖a‖ := by
        rw [norm_smul, norm_smul, Real.norm_of_nonneg (by linarith), Real.norm_of_nonneg hv0]
      _ ≤ (lam + v) * 1 + v * 1 := by gcongr
      _ ≤ 1 := by linarith
  set z : ℝ → Y := fun v => lam⁻¹ • F (x v) with hzdef
  have hz0 : z 0 ∈ C := by
    obtain ⟨e, heC, he⟩ := radial F h0 hF C hext hne q hq hFq lam hlam0.le (by linarith)
    have : z 0 = e := by
      simp only [hzdef, hxdef, add_zero, zero_smul, sub_zero]
      rw [he, smul_smul, inv_mul_cancel₀ hlam0.ne', one_smul]
    rw [this]; exact heC
  have hz_aff : ∀ v, 0 ≤ v → v ≤ 1 / 4 → z v ∈ affineSpan ℝ C := by
    intro v hv0 hv1
    rcases eq_or_lt_of_le hv0 with rfl | hvpos
    · exact subset_affineSpan ℝ C hz0
    · obtain ⟨e, heC, c, hcC, hFx⟩ := mixed F h0 hF C hext hconv hne q a hq ha hFq hFa
        (lam + v) v (by linarith) hvpos (by linarith)
      have hzv : z v = ((2 * v) / lam) • (e -ᵥ c) +ᵥ e := by
        simp only [hzdef, hxdef]
        rw [hFx, vsub_eq_sub, vadd_eq_add]
        have : lam ≠ 0 := hlam0.ne'
        match_scalars <;> field_simp <;> ring
      rw [hzv]
      apply AffineSubspace.vadd_mem_of_mem_direction _ (subset_affineSpan ℝ C heC)
      rw [direction_affineSpan]
      exact Submodule.smul_mem _ _ (vsub_mem_vectorSpan ℝ heC hcC)
  -- the end of the path leaves `λ C`, (4.5)
  have hz1 : z (1 / 4) ∉ C := by
    intro hzC
    have hn1 : ‖z (1 / 4)‖ = 1 := by simpa using hsph hzC
    have hxw : x (1 / 4) - w = lam • q := by
      simp only [hxdef, hw]
      module
    have h1 : ‖F (x (1 / 4)) - F w‖ ≤ lam := by
      calc ‖F (x (1 / 4)) - F w‖ ≤ ‖x (1 / 4) - w‖ :=
            hF _ (hxB _ (by norm_num) le_rfl) _ hwB
        _ = lam * ‖q‖ := by rw [hxw, norm_smul, Real.norm_of_nonneg hlam0.le]
        _ ≤ lam := by nlinarith
    have h2 : ‖F (x (1 / 4))‖ = lam := by
      simp only [hzdef] at hn1
      rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hlam0.le)] at hn1
      field_simp at hn1
      linarith
    have h3 : d ≤ ‖F (x (1 / 4))‖ + ‖F (x (1 / 4)) - F w‖ := by
      have := norm_sub_norm_le (F w) (F (x (1 / 4)))
      rw [norm_sub_rev] at this
      linarith
    linarith
  -- the path, clamped to `[0, 1/4]`, inside the affine span of `C`
  set cl : ℝ → ℝ := fun v => max 0 (min v (1 / 4)) with hcldef
  have hcl0 : ∀ v, 0 ≤ cl v := fun v => le_max_left _ _
  have hcl1 : ∀ v, cl v ≤ 1 / 4 := fun v => max_le (by norm_num) (min_le_right _ _)
  have hclc : Continuous cl := by
    rw [hcldef]; fun_prop
  have hxc : Continuous (fun v => x (cl v)) := by
    rw [hxdef]; fun_prop
  have hFxc : Continuous (fun v => F (x (cl v))) :=
    hFc.comp_continuous hxc (fun v => hxB _ (hcl0 v) (hcl1 v))
  let γ : ℝ → affineSpan ℝ C := fun v => ⟨z (cl v), hz_aff _ (hcl0 v) (hcl1 v)⟩
  have hγ : Continuous γ := by
    apply Continuous.subtype_mk
    rw [hzdef]
    exact hFxc.const_smul _
  -- it crosses the relative boundary, (4.6)
  have hT0 : (0 : ℝ) ∈ γ ⁻¹' ((↑) ⁻¹' C) := by
    show z (cl 0) ∈ C
    have : cl 0 = 0 := by simp [hcldef]
    rw [this]; exact hz0
  have hT1 : (1 / 4 : ℝ) ∉ γ ⁻¹' ((↑) ⁻¹' C) := by
    show z (cl (1 / 4)) ∉ C
    have : cl (1 / 4) = 1 / 4 := by norm_num [hcldef]
    rw [this]; exact hz1
  obtain ⟨v, hv⟩ := (nonempty_frontier_iff (s := γ ⁻¹' ((↑) ⁻¹' C))).mpr
    ⟨⟨0, hT0⟩, fun h => hT1 (h ▸ mem_univ _)⟩
  have hvS := hγ.frontier_preimage_subset _ hv
  have hzfr : z (cl v) ∈ intrinsicFrontier ℝ C := ⟨γ v, hvS, rfl⟩
  obtain ⟨b, hbB, hbq, hFb⟩ := hcov _ hzfr lam hlam0 (by linarith)
  have hlbB : lam • b ∈ closedBall (0 : X) 1 := by
    have hb1 : ‖b‖ ≤ 1 := by simpa using hbB
    rw [mem_closedBall_zero_iff, norm_smul, Real.norm_of_nonneg hlam0.le]
    nlinarith [norm_nonneg b]
  have hFb' : F (lam • b) = F (x (cl v)) := by
    rw [hFb, hzdef]
    simp only
    rw [smul_smul, mul_inv_cancel₀ hlam0.ne', one_smul]
  have hxb : lam • b = x (cl v) := hinj hlbB (hxB _ (hcl0 v) (hcl1 v)) hFb'
  have hv₀pos : 0 < cl v := by
    rcases eq_or_lt_of_le (hcl0 v) with h | h
    · exfalso
      apply hbq
      have hlq : lam • b = lam • q := by
        rw [hxb, hxdef]
        simp only
        rw [← h]
        simp
      exact smul_right_injective X hlam0.ne' hlq
    · exact h
  have hsum : 0 < lam + cl v := by linarith
  refine ⟨b, hbB, cl v / (lam + cl v), lam / (lam + cl v), by positivity, by positivity, ?_, ?_⟩
  · rw [← add_div, add_comm, div_self hsum.ne']
  · have hb' : b = lam⁻¹ • x (cl v) := by
      rw [← hxb, smul_smul, inv_mul_cancel₀ hlam0.ne', one_smul]
    rw [hb', hxdef]
    simp only
    have : lam ≠ 0 := hlam0.ne'
    have : lam + cl v ≠ 0 := hsum.ne'
    match_scalars <;> field_simp <;> ring

end Sol_Plasticity_Faces_exists_isCompact_boundary_preimage_subset

open Sol_Plasticity_Faces_exists_isCompact_boundary_preimage_subset in
theorem solution {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (F : X → Y)
    (hbij : Set.BijOn F (Metric.closedBall (0 : X) 1) (Metric.closedBall (0 : Y) 1))
    (hlip : LipschitzOnWith 1 F (Metric.closedBall (0 : X) 1))
    (C : Set Y) (hC : IsSphereFace C) (hfin : FiniteDimensional ℝ (vectorSpan ℝ C))
    (ih : ∀ C' : Set Y, IsSphereFace C' → C' ⊆ C →
      Module.finrank ℝ (vectorSpan ℝ C') < Module.finrank ℝ (vectorSpan ℝ C) → MatchesFace F C') :
    ∃ K : Set X, IsCompact K ∧ Metric.closedBall (0 : X) 1 ∩ F ⁻¹' (intrinsicFrontier ℝ C) ⊆ K := by
  classical
  obtain ⟨hF0, -, -, -, -⟩ := Sol_Plasticity_Faces_exists_isCompact_boundary_preimage_subset.ballMap_facts F hbij hlip
  have hF1 : ∀ x ∈ Metric.closedBall (0 : X) 1, ∀ y ∈ Metric.closedBall (0 : X) 1,
      ‖F x - F y‖ ≤ ‖x - y‖ :=
    fun x hx y hy => lip_norm hlip hx hy
  obtain ⟨hCcpt, -⟩ := Plasticity.Faces.isCompact_and_eq_closedBall_inter_affineSpan C hC hfin
  have hCcl : IsClosed C := hCcpt.isClosed
  obtain ⟨hCne, hCconv, hCsph, hCext⟩ := hC
  -- Every relative-boundary point lies in a good face of smaller dimension.
  have hbd : ∀ y ∈ intrinsicFrontier ℝ C, ∃ C' : Set Y, C' ⊆ C ∧ IsExtreme ℝ C C' ∧ y ∈ C' ∧
      Module.finrank ℝ (vectorSpan ℝ C') < Module.finrank ℝ (vectorSpan ℝ C) ∧
      MatchesFace F C' := by
    intro y hy
    have hyC : y ∈ C := intrinsicFrontier_subset hCcl hy
    have hyi : y ∉ intrinsicInterior ℝ C := by
      rw [← intrinsicClosure_sdiff_intrinsicInterior] at hy
      exact hy.2
    obtain ⟨C', hC'sub, hC'conv, hC'ext, hyC', hlt⟩ :=
      Plasticity.Aux.exists_proper_face C hCconv hfin y hyC hyi
    have hC'face : IsSphereFace C' :=
      ⟨⟨y, hyC'⟩, hC'conv, hC'sub.trans hCsph, hCext.trans hC'ext⟩
    exact ⟨C', hC'sub, hC'ext, hyC', hlt, ih C' hC'face hC'sub hlt⟩
  -- A preimage `q` of a relative-interior point `c₀`.
  obtain ⟨c₀, hc₀⟩ := ri_nonempty C hCconv hCne hfin
  have hc₀C : c₀ ∈ C := intrinsicInterior_subset hc₀
  have hc₀B : c₀ ∈ Metric.closedBall (0 : Y) 1 := hCext.subset hc₀C
  obtain ⟨q, hqB, hFq⟩ := hbij.surjOn hc₀B
  have hFqC : F q ∈ C := by rw [hFq]; exact hc₀C
  -- Signed boundary preimages: `A = -G(-∂C)` in the form needed.
  have hneg : ∀ a ∈ Metric.closedBall (0 : X) 1, F a ∈ intrinsicFrontier ℝ C → -F (-a) ∈ C := by
    intro a haB haF
    obtain ⟨C', hC'sub, -, hFaC', -, hgood⟩ := hbd (F a) haF
    have h5 := hgood.2.2.2.2.1
    have hmem : -a ∈ Metric.closedBall (0 : X) 1 ∩ F ⁻¹' (-C') := by
      rw [h5, Set.mem_neg, neg_neg]
      exact ⟨haB, hFaC'⟩
    exact hC'sub (Set.mem_neg.mp hmem.2)
  -- Cone coverage of the scaled relative boundary: `t ∂C ⊆ F (t A)`, avoiding `q`.
  have hcov : ∀ y ∈ intrinsicFrontier ℝ C, ∀ t : ℝ, 0 < t → t ≤ 1 →
      ∃ b ∈ Metric.closedBall (0 : X) 1, b ≠ q ∧ F (t • b) = t • y := by
    intro y hy t ht0 ht1
    obtain ⟨C', -, hC'ext, hyC', hlt, hgood⟩ := hbd y hy
    have hcone := hgood.2.2.2.2.2.2.2 t ⟨ht0.le, ht1⟩
    have hty : t • y ∈ F '' (t • (Metric.closedBall (0 : X) 1 ∩ F ⁻¹' C')) := by
      rw [hcone]
      exact Set.smul_mem_smul_set hyC'
    obtain ⟨w, ⟨b, ⟨hbB, hbC'⟩, rfl⟩, hFw⟩ := hty
    refine ⟨b, hbB, ?_, hFw⟩
    rintro rfl
    apply not_mem_proper C C' c₀ hc₀ hC'ext hlt
    rw [← hFq]
    exact hbC'
  by_cases hA : (Metric.closedBall (0 : X) 1 ∩ F ⁻¹' intrinsicFrontier ℝ C).Nonempty
  swap
  · refine ⟨∅, isCompact_empty, ?_⟩
    rw [Set.not_nonempty_iff_eq_empty] at hA
    rw [hA]
  obtain ⟨a₀, ha₀B, ha₀F⟩ := hA
  obtain ⟨E, hE, hEfin, -, hqE, -⟩ := Plasticity.Faces.exists_common_face_of_preimages F hbij hlip C
    ⟨hCne, hCconv, hCsph, hCext⟩ hfin q a₀ hqB ha₀B hFqC (hneg a₀ ha₀B ha₀F)
  refine ⟨E, (Plasticity.Faces.isCompact_and_eq_closedBall_inter_affineSpan E hE hEfin).1, ?_⟩
  rintro a ⟨haB, haF⟩
  have hqa : q ≠ a := by
    rintro rfl
    obtain ⟨C', -, hC'ext, hFC', hlt, -⟩ := hbd (F q) haF
    apply not_mem_proper C C' c₀ hc₀ hC'ext hlt
    rw [← hFq]
    exact hFC'
  obtain ⟨b, hbB, hseg⟩ := crossing F hF0 hF1 hlip.continuousOn hbij.injOn C hCext hCconv hCne
    hCsph q a hqB haB hFqC (hneg a haB haF) hqa hcov
  exact hE.2.2.2.left_mem_of_mem_openSegment haB hbB hqE hseg
