-- Prove2me | solution 1 for Plasticity.Plane.exists_adjacent_edges_of_countable
-- status  : ACCEPTED   (prove)
-- author  : @scanstone
-- created : 2026-10-19T19:03:43.578762+00:00
-- url     : https://prove2.me/submissions/1a74fec0-89c6-442a-95a0-df8064f41c17

import Mathlib.Analysis.Convex.Extreme
import Mathlib.Analysis.Convex.KreinMilman
import Mathlib.Analysis.Convex.Strict.Extreme
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.Module.HahnBanach
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Topology.Baire.CompleteMetrizable
import Mathlib.Tactic.Module
import Mathlib.Tactic.LinearCombination

namespace Sol_Plasticity_Plane_exists_adjacent_edges_of_countable

open Metric Set

section General

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Extreme points of the unit ball of a plane are unit vectors. -/
theorem norm_eq_one (hE : Module.finrank ℝ E = 2) {x : E}
    (hx : x ∈ extremePoints ℝ (closedBall (0 : E) 1)) : ‖x‖ = 1 := by
  have : Nontrivial E := Module.nontrivial_of_finrank_eq_succ hE
  simpa using extremePoints_closedBall_subset_sphere hx

/-- The set of extreme points of the unit ball is symmetric. -/
theorem neg_mem {x : E} (hx : x ∈ extremePoints ℝ (closedBall (0 : E) 1)) :
    -x ∈ extremePoints ℝ (closedBall (0 : E) 1) := by
  rw [mem_extremePoints] at hx ⊢
  refine ⟨by simpa using hx.1, fun y1 hy1 y2 hy2 hseg => ?_⟩
  obtain ⟨p, q, hp, hq, hpq, hpqx⟩ := hseg
  have h := hx.2 (-y1) (by simpa using hy1) (-y2) (by simpa using hy2)
    ⟨p, q, hp, hq, hpq, by rw [smul_neg, smul_neg, ← neg_add, hpqx, neg_neg]⟩
  exact ⟨by rw [← h.1, neg_neg], by rw [← h.2, neg_neg]⟩

/-- A functional of norm at most one is bounded by the norm. -/
theorem abs_le_norm {θ : StrongDual ℝ E} (hθ : ‖θ‖ ≤ 1) (z : E) : |θ z| ≤ ‖z‖ := by
  have h := θ.le_opNorm z
  rw [Real.norm_eq_abs] at h
  calc |θ z| ≤ ‖θ‖ * ‖z‖ := h
    _ ≤ 1 * ‖z‖ := by gcongr
    _ = ‖z‖ := one_mul _

theorem le_norm {θ : StrongDual ℝ E} (hθ : ‖θ‖ ≤ 1) (z : E) : θ z ≤ ‖z‖ :=
  (le_abs_self _).trans (abs_le_norm hθ z)

/-- Two unit vectors that are neither equal nor opposite are linearly independent. -/
theorem indep_of_unit {x y : E} (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) (hxy : x ≠ y) (hxy' : x ≠ -y) :
    LinearIndependent ℝ ![x, y] := by
  rw [LinearIndependent.pair_iff]
  intro s t hst
  by_cases hs : s = 0
  · subst hs
    simp only [zero_smul, zero_add, smul_eq_zero] at hst
    rcases hst with h | h
    · exact ⟨rfl, h⟩
    · simp [h] at hy
  · exfalso
    have hx' : x = (-t / s) • y := by
      have : s • x = -(t • y) := eq_neg_of_add_eq_zero_left hst
      calc x = s⁻¹ • (s • x) := by rw [smul_smul, inv_mul_cancel₀ hs, one_smul]
        _ = (-t / s) • y := by rw [this, smul_neg, smul_smul, ← neg_smul]; congr 1; ring
    have hn : |(-t / s)| = 1 := by
      have := congrArg norm hx'
      rw [norm_smul, hx, hy, Real.norm_eq_abs, mul_one] at this
      exact this.symm
    rcases (abs_eq zero_le_one).mp hn with h | h
    · exact hxy (by rw [hx', h, one_smul])
    · exact hxy' (by rw [hx', h, neg_one_smul])

/-- Coordinates with respect to two independent vectors of a plane. -/
theorem exists_coords (hE : Module.finrank ℝ E = 2) {x y : E} (h : LinearIndependent ℝ ![x, y])
    (v : E) : ∃ α β : ℝ, v = α • x + β • y := by
  let B := basisOfLinearIndependentOfCardEqFinrank h (by simp [hE])
  refine ⟨B.repr v 0, B.repr v 1, ?_⟩
  conv_lhs => rw [← B.sum_repr v]
  rw [Fin.sum_univ_two]
  simp [B, coe_basisOfLinearIndependentOfCardEqFinrank]

/-- A linear map of a plane is determined freely on two independent vectors. -/
theorem exists_linearMap {F : Type*} [AddCommGroup F] [Module ℝ F]
    (hE : Module.finrank ℝ E = 2) {x y : E} (h : LinearIndependent ℝ ![x, y]) (a b : F) :
    ∃ A : E →ₗ[ℝ] F, A x = a ∧ A y = b := by
  let B := basisOfLinearIndependentOfCardEqFinrank h (by simp [hE])
  refine ⟨B.constr ℝ ![a, b], ?_, ?_⟩
  · have := B.constr_basis ℝ ![a, b] 0
    simpa [B, coe_basisOfLinearIndependentOfCardEqFinrank] using this
  · have := B.constr_basis ℝ ![a, b] 1
    simpa [B, coe_basisOfLinearIndependentOfCardEqFinrank] using this

theorem coords_unique {x y : E} (h : LinearIndependent ℝ ![x, y]) {α β α' β' : ℝ}
    (heq : α • x + β • y = α' • x + β' • y) : α = α' ∧ β = β' := by
  have := LinearIndependent.pair_iff.mp h (α - α') (β - β') (by
    rw [sub_smul, sub_smul]
    linear_combination (norm := module) heq)
  exact ⟨by linarith [this.1], by linarith [this.2]⟩

end General

section Collinear

variable {F : Type*} [AddCommGroup F] [Module ℝ F]

/-- Three extreme points on an affine line: one of them is one of the other two. -/
theorem collinear_ext {C : Set F} {x y z : F} (hx : x ∈ extremePoints ℝ C)
    (hy : y ∈ extremePoints ℝ C) (hz : z ∈ extremePoints ℝ C) (hxy : x ≠ y) {σ κ : ℝ}
    (hsum : σ + κ = 1) (hz' : z = σ • x + κ • y) : z = x ∨ z = y := by
  rcases lt_trichotomy σ 0 with hσ | hσ | hσ
  · -- `y` lies strictly between `z` and `x`
    right
    have hκ : 0 < κ := by linarith
    have hseg : y ∈ openSegment ℝ z x := by
      refine ⟨1 / κ, -σ / κ, by positivity, div_pos (by linarith) hκ, ?_, ?_⟩
      · field_simp; linarith
      · have h1 : 1 / κ * σ + -σ / κ = 0 := by field_simp; ring
        have h2 : 1 / κ * κ = 1 := by field_simp
        rw [hz']
        linear_combination (norm := module) h1 • x + h2 • y
    exact ((mem_extremePoints.mp hy).2 z hz.1 x hx.1 hseg).1
  · right
    subst hσ
    have : κ = 1 := by linarith
    rw [hz', this, zero_smul, zero_add, one_smul]
  · rcases lt_trichotomy κ 0 with hκ | hκ | hκ
    · left
      have hseg : x ∈ openSegment ℝ z y := by
        refine ⟨1 / σ, -κ / σ, by positivity, div_pos (by linarith) hσ, ?_, ?_⟩
        · field_simp; linarith
        · have h1 : 1 / σ * κ + -κ / σ = 0 := by field_simp; ring
          have h2 : 1 / σ * σ = 1 := by field_simp
          rw [hz']
          linear_combination (norm := module) h2 • x + h1 • y
      exact ((mem_extremePoints.mp hx).2 z hz.1 y hy.1 hseg).1
    · left
      subst hκ
      have : σ = 1 := by linarith
      rw [hz', this, zero_smul, add_zero, one_smul]
    · exfalso
      have hseg : z ∈ openSegment ℝ x y := ⟨σ, κ, hσ, hκ, hsum, hz'.symm⟩
      have h := (mem_extremePoints.mp hz).2 x hx.1 y hy.1 hseg
      exact hxy (h.1.trans h.2.symm)

end Collinear

section Face

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A functional takes the value one at no more than two extreme points of a planar ball. -/
theorem face_three (hE : Module.finrank ℝ E = 2) {θ : StrongDual ℝ E} {x y z : E}
    (hx : x ∈ extremePoints ℝ (closedBall (0 : E) 1))
    (hy : y ∈ extremePoints ℝ (closedBall (0 : E) 1))
    (hz : z ∈ extremePoints ℝ (closedBall (0 : E) 1))
    (hθx : θ x = 1) (hθy : θ y = 1) (hθz : θ z = 1) (hxy : x ≠ y) : z = x ∨ z = y := by
  have hind := indep_of_unit (norm_eq_one hE hx) (norm_eq_one hE hy) hxy (by
    intro h; rw [h, map_neg] at hθx; linarith)
  obtain ⟨σ, κ, hzc⟩ := exists_coords hE hind z
  have hs : σ + κ = 1 := by
    have := congrArg θ hzc
    simp only [map_add, map_smul, smul_eq_mul, hθx, hθy, hθz] at this
    linarith
  exact collinear_ext hx hy hz hxy hs hzc

/-- A third extreme point is strictly below the face of a functional through two of them. -/
theorem lt_one_of_face (hE : Module.finrank ℝ E = 2) {θ : StrongDual ℝ E} (hθ : ‖θ‖ ≤ 1)
    {x y z : E} (hx : x ∈ extremePoints ℝ (closedBall (0 : E) 1))
    (hy : y ∈ extremePoints ℝ (closedBall (0 : E) 1))
    (hz : z ∈ extremePoints ℝ (closedBall (0 : E) 1))
    (hθx : θ x = 1) (hθy : θ y = 1) (hxy : x ≠ y) (hzx : z ≠ x) (hzy : z ≠ y) : θ z < 1 := by
  have h1 := le_norm hθ z
  rw [norm_eq_one hE hz] at h1
  rcases lt_or_eq_of_le h1 with h | h
  · exact h
  · exfalso
    rcases face_three hE hx hy hz hθx hθy h hxy with h' | h'
    · exact hzx h'
    · exact hzy h'

/-- An edge `[a, b]` (that is, `‖a + b‖ = 2`) has a functional of norm at most one equal to one
at both endpoints. -/
theorem exists_edge_functional {a b : E} (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1) (h2 : ‖a + b‖ = 2) :
    ∃ θ : StrongDual ℝ E, ‖θ‖ ≤ 1 ∧ θ a = 1 ∧ θ b = 1 := by
  obtain ⟨θ, hθ1, hθ⟩ := exists_dual_vector ℝ (a + b) (by rw [h2]; norm_num)
  have h1 := le_norm hθ1.le a
  have h2' := le_norm hθ1.le b
  have hsum : θ a + θ b = 2 := by
    rw [← map_add, hθ, h2]; simp
  exact ⟨θ, hθ1.le, by linarith, by linarith⟩

end Face

section Geometry

variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]

/-- Coordinate functionals of two independent vectors of a plane. -/
theorem exists_coord_maps (hW : Module.finrank ℝ W = 2) {x y : W}
    (h : LinearIndependent ℝ ![x, y]) :
    ∃ f1 f2 : W →ₗ[ℝ] ℝ, ∀ v, v = f1 v • x + f2 v • y := by
  let B := basisOfLinearIndependentOfCardEqFinrank h (by simp [hW])
  refine ⟨B.coord 0, B.coord 1, fun v => ?_⟩
  conv_lhs => rw [← B.sum_repr v]
  rw [Fin.sum_univ_two]
  simp [B, coe_basisOfLinearIndependentOfCardEqFinrank]

/-- A unit vector of a plane that is not an extreme point of the ball lies inside an edge. -/
theorem exists_edge (hW : Module.finrank ℝ W = 2) {z : W} (hz1 : ‖z‖ = 1)
    (hzE : z ∉ extremePoints ℝ (closedBall (0 : W) 1)) :
    ∃ a ∈ extremePoints ℝ (closedBall (0 : W) 1), ∃ b ∈ extremePoints ℝ (closedBall (0 : W) 1),
      a ≠ b ∧ ‖a + b‖ = 2 ∧ z ∈ openSegment ℝ a b := by
  have : FiniteDimensional ℝ W := FiniteDimensional.of_finrank_eq_succ hW
  obtain ⟨θ, hθ1, hθz⟩ := exists_dual_vector ℝ z (by rw [hz1]; norm_num)
  have hθz' : θ z = 1 := by rw [hθz, hz1]; rfl
  set F : Set W := closedBall (0 : W) 1 ∩ {x | θ x = 1} with hF
  have hFc : IsCompact F :=
    (isCompact_closedBall (0 : W) 1).inter_right (isClosed_eq θ.continuous continuous_const)
  have hFconv : Convex ℝ F := by
    refine (convex_closedBall (0 : W) 1).inter ?_
    intro x hx y hy p q hp hq hpq
    simp only [Set.mem_ofPred_eq, map_add, map_smul, smul_eq_mul] at hx hy ⊢
    rw [hx, hy, mul_one, mul_one, hpq]
  have hFext : IsExtreme ℝ (closedBall (0 : W) 1) F := by
    refine ⟨inter_subset_left, fun x1 hx1 x2 hx2 x hx hseg => ?_⟩
    obtain ⟨α, β, hα, hβ, hαβ, rfl⟩ := hseg
    have n1 : ‖x1‖ ≤ 1 := by simpa using hx1
    have n2 : ‖x2‖ ≤ 1 := by simpa using hx2
    have h1 := (le_norm hθ1.le x1).trans n1
    have h2 := (le_norm hθ1.le x2).trans n2
    have hx' : α * θ x1 + β * θ x2 = 1 := by
      have := hx.2
      simp only [Set.mem_ofPred_eq, map_add, map_smul, smul_eq_mul] at this
      exact this
    refine ⟨hx1, ?_⟩
    show θ x1 = 1
    nlinarith [mul_le_mul_of_nonneg_left h2 hβ.le]
  have hsub : extremePoints ℝ F ⊆ extremePoints ℝ (closedBall (0 : W) 1) :=
    hFext.extremePoints_subset_extremePoints
  have hKM : closure (convexHull ℝ (extremePoints ℝ F)) = F :=
    closure_convexHull_extremePoints hFc hFconv
  have hzF : z ∈ F := ⟨by simp [hz1], hθz'⟩
  obtain ⟨p, hp⟩ := hFc.extremePoints_nonempty ⟨z, hzF⟩
  have hpF : p ∈ F := (mem_extremePoints.mp hp).1
  by_cases h : ∃ q ∈ extremePoints ℝ F, q ≠ p
  · obtain ⟨q, hq, hqp⟩ := h
    have hqF : q ∈ F := (mem_extremePoints.mp hq).1
    have hsubpq : extremePoints ℝ F ⊆ {p, q} := by
      intro x hx
      have hxF : x ∈ F := (mem_extremePoints.mp hx).1
      rcases face_three hW (hsub hp) (hsub hq) (hsub hx) hpF.2 hqF.2 hxF.2 hqp.symm with h | h
      · simp [h]
      · simp [h]
    have hFseg : F ⊆ segment ℝ p q := by
      rw [← convexHull_pair]
      conv_lhs => rw [← hKM]
      exact closure_minimal (convexHull_mono (𝕜 := ℝ) hsubpq)
        ((Set.toFinite ({p, q} : Set W)).isCompact_convexHull ℝ).isClosed
    have hzp : p ≠ z := fun h => hzE (h ▸ hsub hp)
    have hzq : q ≠ z := fun h => hzE (h ▸ hsub hq)
    refine ⟨p, hsub hp, q, hsub hq, hqp.symm, ?_,
      mem_openSegment_of_ne_left_right hzp hzq (hFseg hzF)⟩
    apply le_antisymm
    · calc ‖p + q‖ ≤ ‖p‖ + ‖q‖ := norm_add_le _ _
        _ = 2 := by rw [norm_eq_one hW (hsub hp), norm_eq_one hW (hsub hq)]; norm_num
    · have := le_norm hθ1.le (p + q)
      rw [map_add, hpF.2, hqF.2] at this
      linarith
  · push Not at h
    exfalso
    have hFp : F ⊆ {p} := by
      conv_lhs => rw [← hKM]
      have : extremePoints ℝ F ⊆ {p} := fun q hq => h q hq
      exact closure_minimal ((convexHull_mono (𝕜 := ℝ) this).trans (by rw [convexHull_singleton]))
        isClosed_singleton
    have hzp : z = p := hFp hzF
    exact hzE (hzp ▸ hsub hp)

/-- The extreme points of a planar ball form a closed set. -/
theorem isClosed_extremePoints (hW : Module.finrank ℝ W = 2) :
    IsClosed (extremePoints ℝ (closedBall (0 : W) 1)) := by
  have : FiniteDimensional ℝ W := FiniteDimensional.of_finrank_eq_succ hW
  rw [← closure_subset_iff_isClosed]
  intro z hz
  have hz1 : ‖z‖ = 1 := by
    have hsph : extremePoints ℝ (closedBall (0 : W) 1) ⊆ sphere (0 : W) 1 := fun x hx => by
      simp [norm_eq_one hW hx]
    simpa using closure_minimal hsph isClosed_sphere hz
  by_contra hzE
  obtain ⟨a, ha, b, hb, hab, h2, hseg⟩ := exists_edge hW hz1 hzE
  obtain ⟨χ, hχ, hχa, hχb⟩ := exists_edge_functional (norm_eq_one hW ha).le
    (norm_eq_one hW hb).le h2
  have hind : LinearIndependent ℝ ![a, b] := indep_of_unit (norm_eq_one hW ha)
    (norm_eq_one hW hb) hab (by intro h; rw [h, map_neg] at hχa; linarith)
  obtain ⟨f1, f2, hrepr⟩ := exists_coord_maps hW hind
  set U : Set W := {v | 0 < f1 v ∧ 0 < f2 v} with hUdef
  have hU : IsOpen U :=
    (isOpen_lt continuous_const (LinearMap.continuous_of_finiteDimensional f1)).inter
      (isOpen_lt continuous_const (LinearMap.continuous_of_finiteDimensional f2))
  obtain ⟨s, t, hs, ht, hst, hzst⟩ := hseg
  have hzU : z ∈ U := by
    have hco := coords_unique hind (show f1 z • a + f2 z • b = s • a + t • b by
      rw [← hrepr z, hzst])
    exact ⟨by rw [hco.1]; exact hs, by rw [hco.2]; exact ht⟩
  obtain ⟨e, heU, heE⟩ := mem_closure_iff.mp hz U hU hzU
  have he1 : 1 ≤ f1 e + f2 e := by
    calc (1 : ℝ) = ‖e‖ := (norm_eq_one hW heE).symm
      _ = ‖f1 e • a + f2 e • b‖ := by rw [← hrepr e]
      _ ≤ ‖f1 e • a‖ + ‖f2 e • b‖ := norm_add_le _ _
      _ = f1 e + f2 e := by
        rw [norm_smul, norm_smul, norm_eq_one hW ha, norm_eq_one hW hb, Real.norm_eq_abs,
          Real.norm_eq_abs, abs_of_pos heU.1, abs_of_pos heU.2, mul_one, mul_one]
  have he2 : f1 e + f2 e ≤ 1 := by
    have := le_norm hχ e
    rw [norm_eq_one hW heE] at this
    conv_lhs at this => rw [hrepr e]
    simp only [map_add, map_smul, smul_eq_mul, hχa, hχb, mul_one] at this
    exact this
  have hseg' : e ∈ openSegment ℝ a b :=
    ⟨f1 e, f2 e, heU.1, heU.2, le_antisymm he2 he1, (hrepr e).symm⟩
  have := (mem_extremePoints.mp heE).2 a ha.1 b hb.1 hseg'
  exact hab (this.1.trans this.2.symm)

/-- A countable set of extreme points of a planar ball has an isolated point. -/
theorem exists_isolated (hW : Module.finrank ℝ W = 2)
    (hcount : (extremePoints ℝ (closedBall (0 : W) 1)).Countable) :
    ∃ y ∈ extremePoints ℝ (closedBall (0 : W) 1), ∃ r > 0,
      ∀ e ∈ extremePoints ℝ (closedBall (0 : W) 1), ‖e - y‖ < r → e = y := by
  have : FiniteDimensional ℝ W := FiniteDimensional.of_finrank_eq_succ hW
  set E := extremePoints ℝ (closedBall (0 : W) 1) with hE
  have hcl : IsClosed E := isClosed_extremePoints hW
  have : CompleteSpace E := hcl.completeSpace_coe
  have : Countable E := hcount.to_subtype
  obtain ⟨y0, hy0⟩ := (isCompact_closedBall (0 : W) 1).extremePoints_nonempty
    ⟨0, by simp⟩
  have : Nonempty E := ⟨⟨y0, hy0⟩⟩
  obtain ⟨i, hi⟩ := nonempty_interior_of_iUnion_of_closed (X := E)
    (f := fun i : E => ({i} : Set E)) (fun _ => isClosed_singleton)
    (by ext x; simp)
  have hopen : IsOpen ({i} : Set E) := by
    obtain ⟨j, hj⟩ := hi
    have hji : j = i := Set.mem_singleton_iff.mp (interior_subset hj)
    subst hji
    have : interior ({j} : Set E) = {j} :=
      subset_antisymm interior_subset (Set.singleton_subset_iff.mpr hj)
    rw [← this]
    exact isOpen_interior
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hopen i rfl
  refine ⟨i, i.2, r, hr, fun e he hdist => ?_⟩
  have hmem : (⟨e, he⟩ : E) ∈ ({i} : Set E) :=
    hball (by rw [Metric.mem_ball, Subtype.dist_eq, dist_eq_norm]; exact hdist)
  rw [Set.mem_singleton_iff] at hmem
  exact congrArg Subtype.val hmem

/-- Points of segments whose ends stay away from an extreme point stay away from it. -/
theorem exists_sep (hW : Module.finrank ℝ W = 2) {y : W}
    (hy : y ∈ extremePoints ℝ (closedBall (0 : W) 1)) {r : ℝ} (hr : 0 < r) :
    ∃ δ > 0, ∀ a ∈ closedBall (0 : W) 1, ∀ b ∈ closedBall (0 : W) 1, r ≤ ‖a - y‖ →
      r ≤ ‖b - y‖ → ∀ t : ℝ, 0 ≤ t → t ≤ 1 → δ ≤ ‖(1 - t) • a + t • b - y‖ := by
  have : FiniteDimensional ℝ W := FiniteDimensional.of_finrank_eq_succ hW
  set K : Set (W × W × ℝ) := {p | ‖p.1‖ ≤ 1 ∧ r ≤ ‖p.1 - y‖ ∧ ‖p.2.1‖ ≤ 1 ∧
    r ≤ ‖p.2.1 - y‖ ∧ 0 ≤ p.2.2 ∧ p.2.2 ≤ 1} with hKdef
  have hKc : IsCompact K := by
    apply IsCompact.of_isClosed_subset ((isCompact_closedBall (0 : W) 1).prod
      ((isCompact_closedBall (0 : W) 1).prod (isCompact_Icc (a := (0 : ℝ)) (b := 1))))
    · have c1 : IsClosed {p : W × W × ℝ | ‖p.1‖ ≤ 1} :=
        isClosed_le (by fun_prop) continuous_const
      have c2 : IsClosed {p : W × W × ℝ | r ≤ ‖p.1 - y‖} :=
        isClosed_le continuous_const (by fun_prop)
      have c3 : IsClosed {p : W × W × ℝ | ‖p.2.1‖ ≤ 1} :=
        isClosed_le (by fun_prop) continuous_const
      have c4 : IsClosed {p : W × W × ℝ | r ≤ ‖p.2.1 - y‖} :=
        isClosed_le continuous_const (by fun_prop)
      have c5 : IsClosed {p : W × W × ℝ | 0 ≤ p.2.2} :=
        isClosed_le continuous_const (by fun_prop)
      have c6 : IsClosed {p : W × W × ℝ | p.2.2 ≤ 1} :=
        isClosed_le (by fun_prop) continuous_const
      exact c1.inter (c2.inter (c3.inter (c4.inter (c5.inter c6))))
    · rintro p ⟨h1, -, h3, -, h5, h6⟩
      exact ⟨by simpa using h1, by simpa using h3, h5, h6⟩
  set f : W × W × ℝ → ℝ := fun p => ‖(1 - p.2.2) • p.1 + p.2.2 • p.2.1 - y‖ with hfdef
  have hf : Continuous f := by fun_prop
  rcases K.eq_empty_or_nonempty with hK | hK
  · refine ⟨1, one_pos, fun a ha b hb hra hrb t ht0 ht1 => ?_⟩
    exfalso
    have : (a, b, t) ∈ K := ⟨by simpa using ha, hra, by simpa using hb, hrb, ht0, ht1⟩
    rw [hK] at this
    exact this
  · obtain ⟨p0, hp0, hmin⟩ := hKc.exists_isMinOn hK hf.continuousOn
    refine ⟨f p0, ?_, fun a ha b hb hra hrb t ht0 ht1 =>
      (isMinOn_iff.mp hmin) (a, b, t) ⟨by simpa using ha, hra, by simpa using hb, hrb, ht0, ht1⟩⟩
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hp0
    apply lt_of_le_of_ne (norm_nonneg _)
    intro h0
    have heq : (1 - p0.2.2) • p0.1 + p0.2.2 • p0.2.1 = y := sub_eq_zero.mp (norm_eq_zero.mp h0.symm)
    rcases eq_or_lt_of_le h5 with ht0 | ht0
    · rw [← ht0, sub_zero, one_smul, zero_smul, add_zero] at heq
      rw [heq, sub_self, norm_zero] at h2
      linarith
    rcases eq_or_lt_of_le h6 with ht1 | ht1
    · rw [ht1, sub_self, zero_smul, zero_add, one_smul] at heq
      rw [heq, sub_self, norm_zero] at h4
      linarith
    · have hseg : y ∈ openSegment ℝ p0.1 p0.2.1 :=
        ⟨1 - p0.2.2, p0.2.2, by linarith, ht0, by ring, heq⟩
      have := (mem_extremePoints.mp hy).2 _ (by simpa using h1) _ (by simpa using h3) hseg
      rw [this.1, sub_self, norm_zero] at h2
      linarith

/-- Normalizing a small perturbation of a unit vector. -/
theorem normalize_est {y u : W} (hy : ‖y‖ = 1) {s : ℝ} (hs : |s| * ‖u‖ ≤ 1 / 4) :
    3 / 4 ≤ ‖y + s • u‖ ∧ ‖‖y + s • u‖⁻¹ • (y + s • u) - y‖ ≤ 2 * (|s| * ‖u‖) := by
  have hsu : ‖s • u‖ = |s| * ‖u‖ := by rw [norm_smul, Real.norm_eq_abs]
  have hN : |‖y + s • u‖ - 1| ≤ |s| * ‖u‖ := by
    have := abs_norm_sub_norm_le (y + s • u) y
    rwa [hy, add_sub_cancel_left, hsu] at this
  have hN1 : 3 / 4 ≤ ‖y + s • u‖ := by
    have := (abs_le.mp hN).1
    linarith
  refine ⟨hN1, ?_⟩
  set N := ‖y + s • u‖ with hNdef
  have hNpos : 0 < N := by linarith
  calc ‖N⁻¹ • (y + s • u) - y‖ = ‖(N⁻¹ - 1) • (y + s • u) + s • u‖ := by
        congr 1; module
    _ ≤ ‖(N⁻¹ - 1) • (y + s • u)‖ + ‖s • u‖ := norm_add_le _ _
    _ = |1 - N| + |s| * ‖u‖ := by
        rw [norm_smul, ← hNdef, hsu, Real.norm_eq_abs]
        congr 1
        rw [show N⁻¹ - 1 = (1 - N) / N by field_simp, abs_div, abs_of_pos hNpos,
          div_mul_cancel₀ _ hNpos.ne']
    _ ≤ 2 * (|s| * ‖u‖) := by
        rw [abs_sub_comm]
        linarith

end Geometry

end Sol_Plasticity_Plane_exists_adjacent_edges_of_countable

open Sol_Plasticity_Plane_exists_adjacent_edges_of_countable in
theorem solution {W : Type*}
    [NormedAddCommGroup W] [NormedSpace ℝ W] (hW : Module.finrank ℝ W = 2)
    (hcount : (Set.extremePoints ℝ (Metric.closedBall (0 : W) 1)).Countable) :
    ∃ a ∈ Set.extremePoints ℝ (Metric.closedBall (0 : W) 1),
    ∃ b ∈ Set.extremePoints ℝ (Metric.closedBall (0 : W) 1),
    ∃ c ∈ Set.extremePoints ℝ (Metric.closedBall (0 : W) 1),
      a ≠ b ∧ b ≠ c ∧ a ≠ c ∧ ‖a + b‖ = 2 ∧ ‖b + c‖ = 2 := by
  have : FiniteDimensional ℝ W := FiniteDimensional.of_finrank_eq_succ hW
  obtain ⟨y, hy, r, hr, hiso⟩ := exists_isolated hW hcount
  obtain ⟨δ, hδ, hsep⟩ := exists_sep hW hy hr
  set ρ := min r δ with hρ
  have hρpos : 0 < ρ := lt_min hr hδ
  have hy1 : ‖y‖ = 1 := norm_eq_one hW hy
  -- every unit vector close to `y` lies inside an edge ending at `y`
  have hedge : ∀ z : W, ‖z‖ = 1 → z ≠ y → ‖z - y‖ < ρ →
      ∃ c ∈ Set.extremePoints ℝ (Metric.closedBall (0 : W) 1), c ≠ y ∧ ‖y + c‖ = 2 ∧
        z ∈ openSegment ℝ y c := by
    intro z hz1 hzy hzρ
    have hzE : z ∉ Set.extremePoints ℝ (Metric.closedBall (0 : W) 1) := fun h =>
      hzy (hiso z h (lt_of_lt_of_le hzρ (min_le_left _ _)))
    obtain ⟨a, ha, b, hb, hab, h2, hseg⟩ := exists_edge hW hz1 hzE
    by_cases hay : a = y
    · subst hay
      exact ⟨b, hb, hab.symm, h2, hseg⟩
    by_cases hby : b = y
    · subst hby
      exact ⟨a, ha, hab, by rw [add_comm]; exact h2, by rw [openSegment_symm]; exact hseg⟩
    exfalso
    have hra : r ≤ ‖a - y‖ := by
      by_contra h
      push Not at h
      exact hay (hiso a ha h)
    have hrb : r ≤ ‖b - y‖ := by
      by_contra h
      push Not at h
      exact hby (hiso b hb h)
    obtain ⟨α, β, hα, hβ, hαβ, hz⟩ := hseg
    have h3 := hsep a ha.1 b hb.1 hra hrb β hβ.le (by linarith)
    rw [show 1 - β = α by linarith, hz] at h3
    have := min_le_right r δ
    linarith
  -- a direction independent of `y`
  obtain ⟨u, hu⟩ : ∃ u : W, u ∉ Submodule.span ℝ {y} := by
    by_contra h
    push Not at h
    have htop : Submodule.span ℝ {y} = ⊤ := eq_top_iff.mpr (fun u _ => h u)
    have h1 := finrank_span_singleton (K := ℝ) (v := y) (by rintro rfl; simp at hy1)
    rw [htop, finrank_top, hW] at h1
    norm_num at h1
  have hind : LinearIndependent ℝ ![y, u] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    by_cases ht : t = 0
    · subst ht
      rw [zero_smul, add_zero] at hst
      rcases smul_eq_zero.mp hst with h | h
      · exact ⟨h, rfl⟩
      · rw [h, norm_zero] at hy1; norm_num at hy1
    · exfalso
      apply hu
      have hu' : u = (-s / t) • y := by
        have h' : t • u = -(s • y) := eq_neg_of_add_eq_zero_right hst
        calc u = t⁻¹ • (t • u) := by rw [smul_smul, inv_mul_cancel₀ ht, one_smul]
          _ = (-s / t) • y := by rw [h', smul_neg, smul_smul, ← neg_smul]; congr 1; ring
      rw [hu']
      exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self y)
  obtain ⟨f1, f2, hrepr⟩ := exists_coord_maps hW hind
  have hf2y : f2 y = 0 := by
    have := coords_unique hind
      (show f1 y • y + f2 y • u = (1 : ℝ) • y + (0 : ℝ) • u by rw [← hrepr y]; simp)
    exact this.2
  have hf2u : f2 u = 1 := by
    have := coords_unique hind
      (show f1 u • y + f2 u • u = (0 : ℝ) • y + (1 : ℝ) • u by rw [← hrepr u]; simp)
    exact this.2
  -- the step size
  set ε : ℝ := min (ρ / (4 * (‖u‖ + 1))) (1 / (4 * (‖u‖ + 1))) with hεdef
  have hu0 : 0 < ‖u‖ + 1 := by positivity
  have hε : 0 < ε := lt_min (by positivity) (by positivity)
  have hεu1 : ε * ‖u‖ ≤ 1 / 4 := by
    have h1 : ε ≤ 1 / (4 * (‖u‖ + 1)) := min_le_right _ _
    calc ε * ‖u‖ ≤ 1 / (4 * (‖u‖ + 1)) * (‖u‖ + 1) := by
          gcongr
          · linarith
    _ = 1 / 4 := by field_simp
  have hεu2 : 2 * (ε * ‖u‖) < ρ := by
    have h1 : ε ≤ ρ / (4 * (‖u‖ + 1)) := min_le_left _ _
    calc 2 * (ε * ‖u‖) ≤ 2 * (ρ / (4 * (‖u‖ + 1)) * (‖u‖ + 1)) := by
          gcongr
          · linarith
      _ = ρ / 2 := by field_simp; ring
      _ < ρ := by linarith
  -- the two perturbed unit vectors lie inside edges at `y`
  have hpt : ∀ s : ℝ, |s| = ε → 3 / 4 ≤ ‖y + s • u‖ ∧
      ∃ c ∈ Set.extremePoints ℝ (Metric.closedBall (0 : W) 1), c ≠ y ∧ ‖y + c‖ = 2 ∧
        ‖y + s • u‖⁻¹ • (y + s • u) ∈ openSegment ℝ y c := by
    intro s hs
    have hs' : |s| * ‖u‖ ≤ 1 / 4 := by rw [hs]; exact hεu1
    obtain ⟨hN, hdist⟩ := normalize_est hy1 hs'
    refine ⟨hN, hedge _ ?_ ?_ ?_⟩
    · rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (by linarith)]
    · intro h
      have h2 := congrArg f2 h
      rw [map_smul, map_add, map_smul, hf2y, hf2u, smul_eq_mul, smul_eq_mul, zero_add,
        mul_one] at h2
      have hs0 : s ≠ 0 := by
        intro h0
        rw [h0, abs_zero] at hs
        linarith
      rcases mul_eq_zero.mp h2 with h3 | h3
      · exact (inv_ne_zero (by linarith : ‖y + s • u‖ ≠ 0)) h3
      · exact hs0 h3
    · calc ‖‖y + s • u‖⁻¹ • (y + s • u) - y‖ ≤ 2 * (|s| * ‖u‖) := hdist
        _ < ρ := by rw [hs]; exact hεu2
  obtain ⟨hNp, cp, hcp, hcpy, hcp2, hsegp⟩ := hpt ε (abs_of_pos hε)
  obtain ⟨hNm, cm, hcm, hcmy, hcm2, hsegm⟩ := hpt (-ε) (by rw [abs_neg, abs_of_pos hε])
  have hne : cp ≠ cm := by
    intro heq
    rw [← heq] at hsegm
    obtain ⟨α, β, hα, hβ, hαβ, hzp⟩ := hsegp
    obtain ⟨α', β', hα', hβ', hαβ', hzm⟩ := hsegm
    have e1 := congrArg f2 hzp
    have e2 := congrArg f2 hzm
    simp only [map_add, map_smul, smul_eq_mul, hf2y, hf2u, mul_zero, zero_add, mul_one] at e1 e2
    have p1 : 0 < ‖y + ε • u‖⁻¹ * ε := mul_pos (inv_pos.mpr (by linarith)) hε
    have p2 : ‖y + (-ε) • u‖⁻¹ * (-ε) < 0 :=
      mul_neg_of_pos_of_neg (inv_pos.mpr (by linarith)) (by linarith)
    rw [← e1] at p1
    rw [← e2] at p2
    have q1 : 0 < f2 cp := pos_of_mul_pos_right p1 hβ.le
    nlinarith
  exact ⟨cp, hcp, y, hy, cm, hcm, hcpy, hcmy.symm, hne, by rw [add_comm]; exact hcp2, hcm2⟩
