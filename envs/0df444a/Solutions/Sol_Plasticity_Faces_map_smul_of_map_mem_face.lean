-- Prove2me | solution 1 for Plasticity.Faces.map_smul_of_map_mem_face
-- status  : ACCEPTED   (prove)
-- author  : @scanstone
-- created : 2026-10-15T02:26:10.367683+00:00
-- url     : https://prove2.me/submissions/26b1aea0-eb05-4fe3-a1ae-9527d1f0cf90

import Definitions.Def_Plasticity_Faces
import Mathlib.Topology.EMetricSpace.Lipschitz
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Convex.Intrinsic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Theorems.Thm_Plasticity_Faces_matchesFace_of_finiteDimensional
import Theorems.Thm_Plasticity_BallMap_norm_map_sub_map_eq_of_map_smul
import Theorems.Thm_Plasticity_Topology_norm_map_sub_map_eq_of_intrinsicFrontier
import Theorems.Thm_Plasticity_Topology_eq_of_norm_sub_eq_on_intrinsicFrontier
import Theorems.Thm_Plasticity_BallMap_map_zero_of_surjOn
import Theorems.Thm_Plasticity_Aux_exists_proper_face
import Theorems.Thm_Plasticity_Faces_isCompact_and_eq_closedBall_inter_affineSpan

open Plasticity
open scoped Pointwise

namespace Sol_Plasticity_Faces_map_smul_of_map_mem_face

open Set Metric

variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]

/-- The reflected set `-C` has the same direction as `C`. -/
theorem vectorSpan_neg (C : Set Y) : vectorSpan ℝ (-C) = vectorSpan ℝ C := by
  have key : ∀ S : Set Y, vectorSpan ℝ (-S) ≤ vectorSpan ℝ S := by
    intro S
    rw [vectorSpan_def, Submodule.span_le]
    rintro _ ⟨p, hp, q, hq, rfl⟩
    have h : p -ᵥ q = (-q) -ᵥ (-p) := by
      simp only [vsub_eq_sub]
      abel
    show p -ᵥ q ∈ vectorSpan ℝ S
    rw [h]
    exact vsub_mem_vectorSpan ℝ (Set.mem_neg.mp hq) (Set.mem_neg.mp hp)
  refine le_antisymm (key C) ?_
  simpa using key (-C)

/-- The reflection of a sphere face is a sphere face. -/
theorem isSphereFace_neg {C : Set Y} (hC : IsSphereFace C) : IsSphereFace (-C) := by
  obtain ⟨⟨c, hc⟩, hconv, hsph, hext⟩ := hC
  refine ⟨⟨-c, by simpa using hc⟩, hconv.neg, ?_, ⟨?_, ?_⟩⟩
  · intro y hy
    have := hsph (Set.mem_neg.mp hy)
    simpa using this
  · intro y hy
    have := hext.subset (Set.mem_neg.mp hy)
    simpa using this
  · intro x₁ hx₁ x₂ hx₂ x hx hseg
    have hseg' : -x ∈ openSegment ℝ (-x₁) (-x₂) := by
      obtain ⟨a, b, ha, hb, hab, rfl⟩ := hseg
      exact ⟨a, b, ha, hb, hab, by rw [smul_neg, smul_neg, neg_add]⟩
    have h := hext.left_mem_of_mem_openSegment (by simpa using hx₁) (by simpa using hx₂)
      (Set.mem_neg.mp hx) hseg'
    exact Set.mem_neg.mpr h

/-- Every point whose image lies in the relative boundary of a finite-dimensional sphere face is
homogeneous, given homogeneity over all sphere faces of smaller dimension. -/
theorem bd_homog (F : X → Y) (C : Set Y) (hC : IsSphereFace C)
    (hfin : FiniteDimensional ℝ (vectorSpan ℝ C))
    (ih : ∀ C' : Set Y, IsSphereFace C' → FiniteDimensional ℝ (vectorSpan ℝ C') →
      Module.finrank ℝ (vectorSpan ℝ C') < Module.finrank ℝ (vectorSpan ℝ C) →
      ∀ x ∈ closedBall (0 : X) 1, F x ∈ C' → ∀ t ∈ Icc (-1 : ℝ) 1, F (t • x) = t • F x) :
    ∀ b ∈ closedBall (0 : X) 1, F b ∈ intrinsicFrontier ℝ C →
      ∀ t ∈ Icc (-1 : ℝ) 1, F (t • b) = t • F b := by
  intro b hb hFb
  have hCcl : IsClosed C :=
    (Plasticity.Faces.isCompact_and_eq_closedBall_inter_affineSpan C hC hfin).1.isClosed
  have hFbC : F b ∈ C := intrinsicFrontier_subset hCcl hFb
  have hni : F b ∉ intrinsicInterior ℝ C := by
    rw [← intrinsicClosure_sdiff_intrinsicInterior] at hFb
    exact hFb.2
  obtain ⟨C', hC'C, hC'conv, hC'ext, hbC', hdim⟩ :=
    Plasticity.Aux.exists_proper_face C hC.2.1 hfin (F b) hFbC hni
  have hC'sf : IsSphereFace C' :=
    ⟨⟨F b, hbC'⟩, hC'conv, hC'C.trans hC.2.2.1, hC.2.2.2.trans hC'ext⟩
  have hfin' : FiniteDimensional ℝ (vectorSpan ℝ C') :=
    Submodule.finiteDimensional_of_le (vectorSpan_mono ℝ hC'C)
  exact ih C' hC'sf hfin' hdim b hb hbC'

/-- One face at a time: if every point of `D = B_X ∩ F⁻¹(C)` over the relative boundary of `C` is
homogeneous, then `F` is isometric on `D` and `F (t • z) = t • F z` for `z ∈ D`, `0 ≤ t ≤ 1`. -/
theorem per_face (F : X → Y)
    (hbij : BijOn F (closedBall (0 : X) 1) (closedBall (0 : Y) 1))
    (hlip : LipschitzOnWith 1 F (closedBall (0 : X) 1))
    (hsphere : MapsTo F (sphere (0 : X) 1) (sphere (0 : Y) 1))
    (C : Set Y) (hC : IsSphereFace C) (hfin : FiniteDimensional ℝ (vectorSpan ℝ C))
    (hbd : ∀ b ∈ closedBall (0 : X) 1, F b ∈ intrinsicFrontier ℝ C →
      ∀ t ∈ Icc (-1 : ℝ) 1, F (t • b) = t • F b) :
    (∀ z ∈ closedBall (0 : X) 1 ∩ F ⁻¹' C, ∀ z' ∈ closedBall (0 : X) 1 ∩ F ⁻¹' C,
      ‖F z - F z'‖ = ‖z - z'‖) ∧
    (∀ z ∈ closedBall (0 : X) 1 ∩ F ⁻¹' C, ∀ t ∈ Icc (0 : ℝ) 1, F (t • z) = t • F z) := by
  obtain ⟨-, hDc, -, -, -, hbdD, -, hcone⟩ :=
    Plasticity.Faces.matchesFace_of_finiteDimensional F hbij hlip C hC hfin _ rfl
  set D := closedBall (0 : X) 1 ∩ F ⁻¹' C with hD
  have hDcl : IsClosed D := hDc.isClosed
  have hDbdd : Bornology.IsBounded D := hDc.isBounded
  have hDB : D ⊆ closedBall (0 : X) 1 := inter_subset_left
  have hCcl : IsClosed C :=
    (Plasticity.Faces.isCompact_and_eq_closedBall_inter_affineSpan C hC hfin).1.isClosed
  have hCbdd : Bornology.IsBounded C :=
    isBounded_closedBall.subset (hC.2.2.1.trans sphere_subset_closedBall)
  -- boundary points of `D` are homogeneous
  have hbdhom : ∀ b ∈ intrinsicFrontier ℝ D, ∀ t ∈ Icc (-1 : ℝ) 1, F (t • b) = t • F b := by
    intro b hb
    rw [← hbdD] at hb
    exact hbd b hb.1 hb.2
  -- `F` is isometric between boundary points of `D`
  have hfr : ∀ b ∈ intrinsicFrontier ℝ D, ∀ b' ∈ intrinsicFrontier ℝ D,
      ‖F b - F b'‖ = ‖b - b'‖ := by
    intro b hb b' hb'
    exact Plasticity.BallMap.norm_map_sub_map_eq_of_map_smul F hlip hsphere b b'
      (hbdhom b hb) (hbdhom b' hb')
  have hiso : ∀ z ∈ D, ∀ z' ∈ D, ‖F z - F z'‖ = ‖z - z'‖ :=
    Plasticity.Topology.norm_map_sub_map_eq_of_intrinsicFrontier D hDcl hDbdd F (hlip.mono hDB) hfr
  refine ⟨hiso, ?_⟩
  intro z hz t ht
  rcases eq_or_lt_of_le ht.1 with h0 | htpos
  · subst h0
    rw [zero_smul, zero_smul]
    exact Plasticity.BallMap.map_zero_of_surjOn F hbij.surjOn hlip
  -- the rescaled map `g w = t⁻¹ • F (t • w)`
  set g : X → Y := fun w => t⁻¹ • F (t • w) with hg
  have hgB : ∀ w ∈ D, t • w ∈ closedBall (0 : X) 1 := by
    intro w hw
    have hw1 : ‖w‖ ≤ 1 := mem_closedBall_zero_iff.mp hw.1
    rw [mem_closedBall_zero_iff, norm_smul, Real.norm_of_nonneg ht.1]
    nlinarith [norm_nonneg w, ht.2]
  have hglip : LipschitzOnWith 1 g D := by
    apply LipschitzOnWith.of_dist_le_mul
    intro w hw w' hw'
    have h1 := hlip.dist_le_mul _ (hgB w hw) _ (hgB w' hw')
    simp only [dist_eq_norm, NNReal.coe_one, one_mul] at h1 ⊢
    rw [← smul_sub, norm_smul, Real.norm_of_nonneg ht.1] at h1
    simp only [hg]
    rw [← smul_sub, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr ht.1)]
    calc t⁻¹ * ‖F (t • w) - F (t • w')‖ ≤ t⁻¹ * (t * ‖w - w'‖) := by gcongr
      _ = ‖w - w'‖ := by field_simp
  have hgb : ∀ b ∈ intrinsicFrontier ℝ D, g b = F b := by
    intro b hb
    simp only [hg]
    rw [hbdhom b hb t ⟨by linarith [ht.1], ht.2⟩, smul_smul, inv_mul_cancel₀ htpos.ne',
      one_smul]
  have hgiso : ∀ w ∈ D, ∀ w' ∈ D, ‖g w - g w'‖ = ‖w - w'‖ := by
    apply Plasticity.Topology.norm_map_sub_map_eq_of_intrinsicFrontier D hDcl hDbdd g hglip
    intro b hb b' hb'
    rw [hgb b hb, hgb b' hb']
    exact hfr b hb b' hb'
  -- `g z` lies in `C`
  have hgz : g z ∈ C := by
    have h1 : F (t • z) ∈ F '' (t • D) := mem_image_of_mem F (smul_mem_smul_set hz)
    rw [hcone t ht] at h1
    obtain ⟨c, hc, hcz⟩ := mem_smul_set.mp h1
    simp only [hg]
    rw [← hcz, smul_smul, inv_mul_cancel₀ htpos.ne', one_smul]
    exact hc
  -- `g z` and `F z` have the same distance to every relative boundary point of `C`
  have heq : g z = F z := by
    apply Plasticity.Topology.eq_of_norm_sub_eq_on_intrinsicFrontier C hCbdd (g z) (F z) hgz hz.2
    intro c hc
    have hcC : c ∈ C := intrinsicFrontier_subset hCcl hc
    obtain ⟨b, hb, rfl⟩ := hbij.surjOn (sphere_subset_closedBall (hC.2.2.1 hcC))
    have hbD : b ∈ intrinsicFrontier ℝ D := by
      rw [← hbdD]
      exact ⟨hb, hc⟩
    have hbD' : b ∈ D := intrinsicFrontier_subset hDcl hbD
    rw [← hgb b hbD, hgiso z hz b hbD', hgb b hbD, hiso z hz b hbD']
  simp only [hg] at heq
  exact (inv_smul_eq_iff₀ htpos.ne').mp heq

/-- Strong induction on the dimension of the face. -/
theorem homog_aux (F : X → Y)
    (hbij : BijOn F (closedBall (0 : X) 1) (closedBall (0 : Y) 1))
    (hlip : LipschitzOnWith 1 F (closedBall (0 : X) 1))
    (hsphere : MapsTo F (sphere (0 : X) 1) (sphere (0 : Y) 1)) :
    ∀ n : ℕ, ∀ C : Set Y, IsSphereFace C → FiniteDimensional ℝ (vectorSpan ℝ C) →
      Module.finrank ℝ (vectorSpan ℝ C) = n →
      ∀ x ∈ closedBall (0 : X) 1, F x ∈ C → ∀ t ∈ Icc (-1 : ℝ) 1, F (t • x) = t • F x := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n IH =>
  intro C hC hfin hn
  have ih : ∀ C' : Set Y, IsSphereFace C' → FiniteDimensional ℝ (vectorSpan ℝ C') →
      Module.finrank ℝ (vectorSpan ℝ C') < Module.finrank ℝ (vectorSpan ℝ C) →
      ∀ x ∈ closedBall (0 : X) 1, F x ∈ C' → ∀ t ∈ Icc (-1 : ℝ) 1, F (t • x) = t • F x :=
    fun C' hC' hfin' hlt => IH _ (hn ▸ hlt) C' hC' hfin' rfl
  -- the reflected face `-C`
  have hCn : IsSphereFace (-C) := isSphereFace_neg hC
  have hvs : vectorSpan ℝ (-C) = vectorSpan ℝ C := vectorSpan_neg C
  have hfinn : FiniteDimensional ℝ (vectorSpan ℝ (-C)) := by rw [hvs]; exact hfin
  have ihn : ∀ C' : Set Y, IsSphereFace C' → FiniteDimensional ℝ (vectorSpan ℝ C') →
      Module.finrank ℝ (vectorSpan ℝ C') < Module.finrank ℝ (vectorSpan ℝ (-C)) →
      ∀ x ∈ closedBall (0 : X) 1, F x ∈ C' → ∀ t ∈ Icc (-1 : ℝ) 1, F (t • x) = t • F x := by
    rw [hvs]; exact ih
  have hCncl : IsClosed (-C) :=
    (Plasticity.Faces.isCompact_and_eq_closedBall_inter_affineSpan (-C) hCn hfinn).1.isClosed
  have hCnbdd : Bornology.IsBounded (-C) :=
    isBounded_closedBall.subset (hCn.2.2.1.trans sphere_subset_closedBall)
  obtain ⟨hisoP, hscP⟩ := per_face F hbij hlip hsphere C hC hfin (bd_homog F C hC hfin ih)
  obtain ⟨hisoN, hscN⟩ :=
    per_face F hbij hlip hsphere (-C) hCn hfinn (bd_homog F (-C) hCn hfinn ihn)
  obtain ⟨-, -, -, -, hnegD, -⟩ :=
    Plasticity.Faces.matchesFace_of_finiteDimensional F hbij hlip C hC hfin _ rfl
  intro x hx hFx t ht
  have hxD : x ∈ closedBall (0 : X) 1 ∩ F ⁻¹' C := ⟨hx, hFx⟩
  have hnx : -x ∈ closedBall (0 : X) 1 ∩ F ⁻¹' (-C) := by
    rw [hnegD, Set.mem_neg, neg_neg]
    exact hxD
  -- `F (-x) = -F x`
  have hneg : F (-x) = -F x := by
    apply Plasticity.Topology.eq_of_norm_sub_eq_on_intrinsicFrontier (-C) hCnbdd (F (-x)) (-F x)
      hnx.2 (by rw [Set.mem_neg, neg_neg]; exact hFx)
    intro c hc
    have hcC : c ∈ -C := intrinsicFrontier_subset hCncl hc
    obtain ⟨b, hb, rfl⟩ := hbij.surjOn (sphere_subset_closedBall (hCn.2.2.1 hcC))
    have hbh := bd_homog F (-C) hCn hfinn ihn b hb hc
    have hFnb : F (-b) = -F b := by
      have h1 := hbh (-1) ⟨le_refl _, by norm_num⟩
      rwa [neg_one_smul, neg_one_smul] at h1
    have hnbD : -b ∈ closedBall (0 : X) 1 ∩ F ⁻¹' C := by
      refine ⟨by rw [mem_closedBall_zero_iff, norm_neg]; exact mem_closedBall_zero_iff.mp hb, ?_⟩
      show F (-b) ∈ C
      rw [hFnb]
      exact Set.mem_neg.mp hcC
    calc ‖F (-x) - F b‖ = ‖-x - b‖ := hisoN (-x) hnx b ⟨hb, hcC⟩
      _ = ‖x - -b‖ := by rw [← norm_neg]; congr 1; abel
      _ = ‖F x - F (-b)‖ := (hisoP x hxD (-b) hnbD).symm
      _ = ‖-F x - F b‖ := by rw [hFnb, ← norm_neg]; congr 1; abel
  rcases le_total 0 t with h0 | h0
  · exact hscP x hxD t ⟨h0, ht.2⟩
  · have h1 := hscN (-x) hnx (-t) ⟨by linarith, by linarith [ht.1]⟩
    rwa [neg_smul_neg, hneg, neg_smul_neg] at h1

/-- A nonexpansive map of `B_X` whose image covers `B_Y` maps `B_X` into `B_Y`: a point with
`‖F a‖ > 1` and a preimage of `-F a / ‖F a‖` would map more than `2` apart. -/
theorem mapsTo_of_surjOn {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] (F : X → Y)
    (hsurj : Set.SurjOn F (Metric.closedBall (0 : X) 1) (Metric.closedBall (0 : Y) 1))
    (hlip : LipschitzOnWith 1 F (Metric.closedBall (0 : X) 1)) :
    Set.MapsTo F (Metric.closedBall (0 : X) 1) (Metric.closedBall (0 : Y) 1) := by
  intro a ha
  rw [mem_closedBall_zero_iff]
  by_contra hgt
  push_neg at hgt
  have hpos : 0 < ‖F a‖ := lt_trans one_pos hgt
  have hw1 : -(‖F a‖⁻¹ • F a) ∈ Metric.closedBall (0 : Y) 1 := by
    rw [mem_closedBall_zero_iff, norm_neg, norm_smul, norm_inv, norm_norm,
      inv_mul_cancel₀ hpos.ne']
  obtain ⟨b, hb, hFb⟩ := hsurj hw1
  have h1 : ‖F a - F b‖ ≤ ‖a - b‖ := by
    have := hlip.dist_le_mul a ha b hb
    simpa [dist_eq_norm] using this
  have h2 : ‖a - b‖ ≤ 2 := by
    calc ‖a - b‖ ≤ ‖a‖ + ‖b‖ := norm_sub_le a b
      _ ≤ 1 + 1 := add_le_add (mem_closedBall_zero_iff.mp ha) (mem_closedBall_zero_iff.mp hb)
      _ = 2 := by norm_num
  have h3 : ‖F a - F b‖ = ‖F a‖ + 1 := by
    rw [hFb, sub_neg_eq_add]
    have : F a + ‖F a‖⁻¹ • F a = (1 + ‖F a‖⁻¹) • F a := by rw [add_smul, one_smul]
    rw [this, norm_smul, Real.norm_of_nonneg (by positivity), add_mul, one_mul,
      inv_mul_cancel₀ hpos.ne']
  linarith

end Sol_Plasticity_Faces_map_smul_of_map_mem_face

theorem solution {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (F : X → Y)
    (hinj : Set.InjOn F (Metric.closedBall (0 : X) 1))
    (hsurj : Set.SurjOn F (Metric.closedBall (0 : X) 1) (Metric.closedBall (0 : Y) 1))
    (hlip : LipschitzOnWith 1 F (Metric.closedBall (0 : X) 1))
    (hsphere : Set.MapsTo F (Metric.sphere (0 : X) 1) (Metric.sphere (0 : Y) 1))
    (C : Set Y) (hC : IsSphereFace C) (hfin : FiniteDimensional ℝ (vectorSpan ℝ C))
    (x : X) (hx : x ∈ Metric.closedBall (0 : X) 1) (hFx : F x ∈ C) :
    ∀ t ∈ Set.Icc (-1 : ℝ) 1, F (t • x) = t • F x := by
  have hbij : Set.BijOn F (Metric.closedBall (0 : X) 1) (Metric.closedBall (0 : Y) 1) :=
    ⟨Sol_Plasticity_Faces_map_smul_of_map_mem_face.mapsTo_of_surjOn F hsurj hlip, hinj, hsurj⟩
  exact Sol_Plasticity_Faces_map_smul_of_map_mem_face.homog_aux F hbij hlip hsphere _ C hC hfin rfl
    x hx hFx
