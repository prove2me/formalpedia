-- Prove2me | solution 1 for Plasticity.Faces.exists_linearIsometryEquiv_of_sphere_covered_normedSpace
-- status  : ACCEPTED   (prove)
-- author  : @scanstone
-- created : 2026-10-15T02:27:02.50699+00:00
-- url     : https://prove2.me/submissions/ba70c43a-96d6-4527-b419-1abe38d312e8

import Definitions.Def_Plasticity_Faces
import Mathlib.Analysis.Normed.Operator.LinearIsometry
import Mathlib.Analysis.Normed.Affine.MazurUlam
import Mathlib.Topology.EMetricSpace.Lipschitz
import Theorems.Thm_Plasticity_Faces_matchesFace_of_finiteDimensional
import Theorems.Thm_Plasticity_BallMap_map_zero_of_surjOn
import Theorems.Thm_Plasticity_BallMap_norm_map_sub_map_eq_of_map_smul
import Theorems.Thm_Plasticity_Faces_map_smul_of_map_mem_face

open Plasticity
open scoped Pointwise

namespace Sol_Plasticity_Faces_exists_linearIsometryEquiv_of_sphere_covered_normedSpace

open Set Metric

variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]

/-- Step 1. Under the cover hypothesis, `F` maps the unit sphere into the unit sphere. -/
theorem maps_sphere (F : X → Y)
    (hbij : BijOn F (closedBall (0 : X) 1) (closedBall (0 : Y) 1))
    (hlip : LipschitzOnWith 1 F (closedBall (0 : X) 1))
    (hcover : ∀ y ∈ sphere (0 : Y) 1, ∃ C : Set Y,
      IsSphereFace C ∧ FiniteDimensional ℝ (vectorSpan ℝ C) ∧ y ∈ C) :
    MapsTo F (sphere (0 : X) 1) (sphere (0 : Y) 1) := by
  intro x hx
  have hxn : ‖x‖ = 1 := by simpa using hx
  have hxB : x ∈ closedBall (0 : X) 1 := sphere_subset_closedBall hx
  set y := F x with hy
  have hyB : y ∈ closedBall (0 : Y) 1 := hbij.mapsTo hxB
  have hyle : ‖y‖ ≤ 1 := by simpa using hyB
  have hF0 : F 0 = 0 := Plasticity.BallMap.map_zero_of_surjOn F hbij.surjOn hlip
  have h0B : (0 : X) ∈ closedBall (0 : X) 1 := mem_closedBall_self zero_le_one
  have hy0 : y ≠ 0 := by
    intro h
    have : x = 0 := hbij.injOn hxB h0B (by rw [← hy, h, hF0])
    rw [this, norm_zero] at hxn
    exact zero_ne_one hxn
  have hypos : 0 < ‖y‖ := norm_pos_iff.mpr hy0
  set u := ‖y‖⁻¹ • y with hu
  have hun : ‖u‖ = 1 := by
    rw [hu, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hypos.ne']
  have huS : u ∈ sphere (0 : Y) 1 := by simpa using hun
  obtain ⟨C, hC, hfin, huC⟩ := hcover u huS
  obtain ⟨hD, -, -, -, -, -, -, hcone⟩ :=
    Plasticity.Faces.matchesFace_of_finiteDimensional F hbij hlip C hC hfin
      (closedBall (0 : X) 1 ∩ F ⁻¹' C) rfl
  have hyu : ‖y‖ • u = y := by
    rw [hu, smul_smul, mul_inv_cancel₀ hypos.ne', one_smul]
  have hymem : y ∈ F '' (‖y‖ • (closedBall (0 : X) 1 ∩ F ⁻¹' C)) := by
    rw [hcone ‖y‖ ⟨norm_nonneg y, hyle⟩]
    have h := Set.smul_mem_smul_set (a := ‖y‖) huC
    rwa [hyu] at h
  obtain ⟨z, hz, hFz⟩ := hymem
  obtain ⟨d, hd, rfl⟩ := Set.mem_smul_set.mp hz
  have hdS : d ∈ sphere (0 : X) 1 := hD.2.2.1 hd
  have hdn : ‖d‖ = 1 := by simpa using hdS
  have hzn : ‖‖y‖ • d‖ = ‖y‖ := by rw [norm_smul, norm_norm, hdn, mul_one]
  have hzB : ‖y‖ • d ∈ closedBall (0 : X) 1 := by
    rw [mem_closedBall_zero_iff, hzn]; exact hyle
  have hzx : ‖y‖ • d = x := hbij.injOn hzB hxB (by rw [hFz])
  have : ‖y‖ = 1 := by rw [← hzn, hzx, hxn]
  simpa using this

/-- A point rescaled by `R ≥ max 1 ‖x‖` lies in the closed unit ball. -/
theorem inv_smul_mem_closedBall {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (x : E) (R : ℝ) (hR : max 1 ‖x‖ ≤ R) : R⁻¹ • x ∈ closedBall (0 : E) 1 := by
  have hR0 : 0 < R := lt_of_lt_of_le one_pos ((le_max_left _ _).trans hR)
  rw [mem_closedBall_zero_iff, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hR0.le),
    inv_mul_le_iff₀ hR0, mul_one]
  exact (le_max_right _ _).trans hR

/-- Step 3 on every ray. Under the cover hypothesis, every point of `B_X` is homogeneous. -/
theorem homog_all (F : X → Y)
    (hbij : BijOn F (closedBall (0 : X) 1) (closedBall (0 : Y) 1))
    (hlip : LipschitzOnWith 1 F (closedBall (0 : X) 1))
    (hcover : ∀ y ∈ sphere (0 : Y) 1, ∃ C : Set Y,
      IsSphereFace C ∧ FiniteDimensional ℝ (vectorSpan ℝ C) ∧ y ∈ C) :
    ∀ x ∈ closedBall (0 : X) 1, ∀ t ∈ Icc (-1 : ℝ) 1, F (t • x) = t • F x := by
  have hs := maps_sphere F hbij hlip hcover
  have hF0 : F 0 = 0 := Plasticity.BallMap.map_zero_of_surjOn F hbij.surjOn hlip
  intro x hx t ht
  rcases eq_or_ne x 0 with rfl | hx0
  · rw [smul_zero, hF0, smul_zero]
  have hxpos : 0 < ‖x‖ := norm_pos_iff.mpr hx0
  have hxle : ‖x‖ ≤ 1 := mem_closedBall_zero_iff.mp hx
  set u := ‖x‖⁻¹ • x with hu
  have hun : ‖u‖ = 1 := by
    rw [hu, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hxpos.ne']
  have huS : u ∈ sphere (0 : X) 1 := by simpa using hun
  obtain ⟨C, hC, hfin, hFuC⟩ := hcover (F u) (hs huS)
  have hhom := Plasticity.Faces.map_smul_of_map_mem_face F hbij.injOn hbij.surjOn hlip hs C hC hfin u
    (sphere_subset_closedBall huS) hFuC
  have hxu : x = ‖x‖ • u := by
    rw [hu, smul_smul, mul_inv_cancel₀ hxpos.ne', one_smul]
  have h1 : F x = ‖x‖ • F u := by
    calc F x = F (‖x‖ • u) := congrArg F hxu
      _ = ‖x‖ • F u := hhom ‖x‖ ⟨by linarith, hxle⟩
  have h2 : F (t • x) = (t * ‖x‖) • F u := by
    calc F (t • x) = F ((t * ‖x‖) • u) := by rw [← smul_smul, ← hxu]
      _ = (t * ‖x‖) • F u :=
        hhom _ ⟨by nlinarith [ht.1, ht.2, hxpos.le], by nlinarith [ht.1, ht.2, hxpos.le]⟩
  rw [h2, h1, smul_smul]

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

end Sol_Plasticity_Faces_exists_linearIsometryEquiv_of_sphere_covered_normedSpace

open Set Metric in
theorem solution {X Y : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (F : X → Y)
    (hinj : Set.InjOn F (Metric.closedBall (0 : X) 1))
    (hsurj : Set.SurjOn F (Metric.closedBall (0 : X) 1) (Metric.closedBall (0 : Y) 1))
    (hlip : LipschitzOnWith 1 F (Metric.closedBall (0 : X) 1))
    (hcover : ∀ y ∈ Metric.sphere (0 : Y) 1, ∃ C : Set Y,
      IsSphereFace C ∧ FiniteDimensional ℝ (vectorSpan ℝ C) ∧ y ∈ C) :
    ∃ T : X ≃ₗᵢ[ℝ] Y, Set.EqOn F T (Metric.closedBall (0 : X) 1) := by
  have hbij : Set.BijOn F (Metric.closedBall (0 : X) 1) (Metric.closedBall (0 : Y) 1) :=
    ⟨Sol_Plasticity_Faces_exists_linearIsometryEquiv_of_sphere_covered_normedSpace.mapsTo_of_surjOn F hsurj hlip, hinj, hsurj⟩
  have hs := Sol_Plasticity_Faces_exists_linearIsometryEquiv_of_sphere_covered_normedSpace.maps_sphere
    F hbij hlip hcover
  have hhom :=
    Sol_Plasticity_Faces_exists_linearIsometryEquiv_of_sphere_covered_normedSpace.homog_all
      F hbij hlip hcover
  have hF0 : F 0 = 0 := Plasticity.BallMap.map_zero_of_surjOn F hbij.surjOn hlip
  -- Step 2: `F` is isometric on `B_X`
  have hiso : ∀ x ∈ closedBall (0 : X) 1, ∀ y ∈ closedBall (0 : X) 1, ‖F x - F y‖ = ‖x - y‖ :=
    fun x hx y hy => Plasticity.BallMap.norm_map_sub_map_eq_of_map_smul F hlip hs x y
      (hhom x hx) (hhom y hy)
  -- Step 4: the positively homogeneous extension
  set T : X → Y := fun x => (max 1 ‖x‖) • F ((max 1 ‖x‖)⁻¹ • x) with hT
  have hinB : ∀ x : X, ∀ R : ℝ, max 1 ‖x‖ ≤ R → R⁻¹ • x ∈ closedBall (0 : X) 1 :=
    Sol_Plasticity_Faces_exists_linearIsometryEquiv_of_sphere_covered_normedSpace.inv_smul_mem_closedBall
  have hkey : ∀ x : X, ∀ R : ℝ, max 1 ‖x‖ ≤ R → T x = R • F (R⁻¹ • x) := by
    intro x R hR
    set r := max 1 ‖x‖ with hr
    have hr0 : 0 < r := lt_of_lt_of_le one_pos (le_max_left _ _)
    have hR0 : 0 < R := lt_of_lt_of_le hr0 hR
    have hv : r⁻¹ • x ∈ closedBall (0 : X) 1 := hinB x r le_rfl
    have hRx : R⁻¹ • x = (r / R) • (r⁻¹ • x) := by
      rw [smul_smul]
      congr 1
      field_simp
    have hc : r / R ∈ Icc (-1 : ℝ) 1 :=
      ⟨by linarith [div_nonneg hr0.le hR0.le], (div_le_one hR0).mpr hR⟩
    have hRr : R * (r / R) = r := by field_simp
    calc T x = r • F (r⁻¹ • x) := rfl
      _ = R • F (R⁻¹ • x) := by rw [hRx, hhom _ hv _ hc, smul_smul, hRr]
  have hTiso : Isometry T := by
    apply Isometry.of_dist_eq
    intro x y
    set R := max (max 1 ‖x‖) (max 1 ‖y‖) with hRdef
    have hRx : max 1 ‖x‖ ≤ R := le_max_left _ _
    have hRy : max 1 ‖y‖ ≤ R := le_max_right _ _
    have hR0 : 0 < R := lt_of_lt_of_le one_pos ((le_max_left _ _).trans hRx)
    rw [dist_eq_norm, dist_eq_norm, hkey x R hRx, hkey y R hRy, ← smul_sub, norm_smul,
      Real.norm_of_nonneg hR0.le, hiso _ (hinB x R hRx) _ (hinB y R hRy), ← smul_sub, norm_smul,
      Real.norm_of_nonneg (inv_nonneg.mpr hR0.le), ← mul_assoc, mul_inv_cancel₀ hR0.ne', one_mul]
  have hTsurj : Function.Surjective T := by
    intro y
    set r := max 1 ‖y‖ with hr
    have hr0 : 0 < r := lt_of_lt_of_le one_pos (le_max_left _ _)
    obtain ⟨z, hz, hFz⟩ := hbij.surjOn
      (Sol_Plasticity_Faces_exists_linearIsometryEquiv_of_sphere_covered_normedSpace.inv_smul_mem_closedBall
        y r le_rfl)
    refine ⟨r • z, ?_⟩
    have hzle : ‖z‖ ≤ 1 := mem_closedBall_zero_iff.mp hz
    have hrz : max 1 ‖r • z‖ ≤ r := by
      refine max_le (le_max_left _ _) ?_
      rw [norm_smul, Real.norm_of_nonneg hr0.le]
      nlinarith [norm_nonneg z]
    rw [hkey (r • z) r hrz, smul_smul, inv_mul_cancel₀ hr0.ne', one_smul, hFz, smul_smul,
      mul_inv_cancel₀ hr0.ne', one_smul]
  have hT0 : T 0 = 0 := by
    simp only [hT, smul_zero, hF0]
  have hEq : EqOn F T (closedBall (0 : X) 1) := by
    intro x hx
    have h1 : max 1 ‖x‖ ≤ 1 := max_le le_rfl (mem_closedBall_zero_iff.mp hx)
    rw [hkey x 1 h1, inv_one, one_smul, one_smul]
  let e : X ≃ᵢ Y :=
    { Equiv.ofBijective T ⟨hTiso.injective, hTsurj⟩ with isometry_toFun := hTiso }
  have he0 : e 0 = 0 := hT0
  refine ⟨e.toRealLinearIsometryEquivOfMapZero he0, fun x hx => ?_⟩
  -- Mazur–Ulam: the linear isometry is `e = T` as a function
  exact hEq hx
