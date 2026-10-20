-- Prove2me | solution 1 for Plasticity.Plane.exists_linearIsometryEquiv_of_radial_le_uncountable
-- status  : ACCEPTED   (prove)
-- author  : @scanstone
-- created : 2026-10-19T19:03:47.898894+00:00
-- url     : https://prove2.me/submissions/d060ffe4-e5ab-47c9-b00d-07723df921a8

import Mathlib.Analysis.Convex.Extreme
import Mathlib.Analysis.Convex.Strict.Extreme
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.Module.HahnBanach
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Operator.LinearIsometry
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Topology.Bases
import Mathlib.Tactic.Module
import Mathlib.Tactic.LinearCombination
import Theorems.Thm_Plasticity_Plane_exists_linearIsometryEquiv_of_contraction_of_extremePoints

namespace Sol_Plasticity_Plane_exists_linearIsometryEquiv_of_radial_le_uncountable

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

section Smooth

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- The functionals at which the evaluation at `v` equals the norm on a whole neighbourhood
determine `v`. -/
theorem eq_of_open {d : StrongDual ℝ V} {v v' : V}
    (hv : ∃ U : Set (StrongDual ℝ V), IsOpen U ∧ d ∈ U ∧ ∀ θ ∈ U, θ v = ‖θ‖)
    (hv' : ∃ U : Set (StrongDual ℝ V), IsOpen U ∧ d ∈ U ∧ ∀ θ ∈ U, θ v' = ‖θ‖) : v = v' := by
  obtain ⟨U, hU, hdU, hUv⟩ := hv
  obtain ⟨U', hU', hdU', hUv'⟩ := hv'
  have hO : IsOpen (U ∩ U') := hU.inter hU'
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hO d ⟨hdU, hdU'⟩
  have hzero : ∀ θ ∈ U ∩ U', θ (v - v') = 0 := by
    intro θ hθ
    rw [map_sub, hUv θ hθ.1, hUv' θ hθ.2, sub_self]
  have hall : ∀ η : StrongDual ℝ V, η (v - v') = 0 := by
    intro η
    set t : ℝ := ε / (2 * (‖η‖ + 1)) with ht
    have ht0 : 0 < t := by positivity
    have hmem : d + t • η ∈ U ∩ U' := by
      apply hball
      rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
        abs_of_pos ht0, ht]
      have h1 : ‖η‖ < 2 * (‖η‖ + 1) := by linarith [norm_nonneg η]
      calc ε / (2 * (‖η‖ + 1)) * ‖η‖ < ε / (2 * (‖η‖ + 1)) * (2 * (‖η‖ + 1)) := by
            gcongr
        _ = ε := by field_simp
    have h1 := hzero _ hmem
    have h2 := hzero d ⟨hdU, hdU'⟩
    rw [add_apply, smul_apply, h2, zero_add,
      smul_eq_mul] at h1
    rcases mul_eq_zero.mp h1 with h | h
    · exact absurd h ht0.ne'
    · exact h
  by_contra hne
  have hx : ‖v - v'‖ ≠ 0 := by rw [norm_ne_zero_iff, sub_ne_zero]; exact hne
  obtain ⟨η, -, hη⟩ := exists_dual_vector ℝ (v - v') hx
  rw [hall η] at hη
  exact hx (by simpa using hη.symm)

/-- In a plane, the unit vectors with two different norming functionals form a countable
set. -/
theorem countable_nonsmooth (hV : Module.finrank ℝ V = 2) :
    {v : V | ‖v‖ = 1 ∧ ∃ φ1 φ2 : StrongDual ℝ V, ‖φ1‖ ≤ 1 ∧ ‖φ2‖ ≤ 1 ∧ φ1 v = 1 ∧ φ2 v = 1 ∧
      φ1 ≠ φ2}.Countable := by
  have : FiniteDimensional ℝ V := FiniteDimensional.of_finrank_eq_succ hV
  have hdual : Module.finrank ℝ (StrongDual ℝ V) = 2 := by
    rw [← (LinearMap.toContinuousLinearMap (𝕜 := ℝ) (E := V) (F' := ℝ)).finrank_eq]
    exact (Subspace.dual_finrank_eq).trans hV
  obtain ⟨D, hDc, hDd⟩ := TopologicalSpace.exists_countable_dense (StrongDual ℝ V)
  let T : StrongDual ℝ V → Set V := fun d =>
    {v | ∃ U : Set (StrongDual ℝ V), IsOpen U ∧ d ∈ U ∧ ∀ θ ∈ U, θ v = ‖θ‖}
  have hT : ∀ d, (T d).Countable := fun d =>
    Set.Subsingleton.countable (fun v hv v' hv' => eq_of_open hv hv')
  refine (hDc.biUnion fun d _ => hT d).mono ?_
  rintro v ⟨hv1, φ1, φ2, hφ1, hφ2, hφ1v, hφ2v, hne⟩
  have hind : LinearIndependent ℝ ![φ1, φ2] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    have h1 := congrArg (fun θ : StrongDual ℝ V => θ v) hst
    simp only [add_apply, smul_apply, hφ1v, hφ2v,
      smul_eq_mul, mul_one, zero_apply] at h1
    have ht : t = -s := by linarith
    subst ht
    have h2 : s • (φ1 - φ2) = 0 := by rw [smul_sub, sub_eq_add_neg, ← neg_smul]; exact hst
    rcases smul_eq_zero.mp h2 with h | h
    · exact ⟨h, by rw [h, neg_zero]⟩
    · exact absurd (sub_eq_zero.mp h) hne
  let B := basisOfLinearIndependentOfCardEqFinrank hind (by simp [hdual])
  have hB0 : B 0 = φ1 := by simp [B, coe_basisOfLinearIndependentOfCardEqFinrank]
  have hB1 : B 1 = φ2 := by simp [B, coe_basisOfLinearIndependentOfCardEqFinrank]
  let c0 : StrongDual ℝ V →ₗ[ℝ] ℝ := B.coord 0
  let c1 : StrongDual ℝ V →ₗ[ℝ] ℝ := B.coord 1
  let U : Set (StrongDual ℝ V) := {θ | 0 < c0 θ ∧ 0 < c1 θ}
  have hU : IsOpen U :=
    (isOpen_lt continuous_const (LinearMap.continuous_of_finiteDimensional c0)).inter
      (isOpen_lt continuous_const (LinearMap.continuous_of_finiteDimensional c1))
  have hrepr : ∀ θ : StrongDual ℝ V, θ = c0 θ • φ1 + c1 θ • φ2 := by
    intro θ
    conv_lhs => rw [← B.sum_repr θ]
    rw [Fin.sum_univ_two, hB0, hB1]
    rfl
  have hUne : (φ1 + φ2) ∈ U := by
    have e0 : c0 (φ1 + φ2) = 1 := by
      simp only [c0, Module.Basis.coord_apply, map_add, ← hB0, ← hB1, Module.Basis.repr_self]
      simp
    have e1 : c1 (φ1 + φ2) = 1 := by
      simp only [c1, Module.Basis.coord_apply, map_add, ← hB0, ← hB1, Module.Basis.repr_self]
      simp
    exact ⟨by rw [e0]; exact one_pos, by rw [e1]; exact one_pos⟩
  obtain ⟨d, hdD, hdU⟩ := hDd.exists_mem_open hU ⟨_, hUne⟩
  refine Set.mem_biUnion hdD ⟨U, hU, hdU, fun θ hθ => ?_⟩
  have hθv : θ v = c0 θ + c1 θ := by
    conv_lhs => rw [hrepr θ]
    simp [hφ1v, hφ2v]
  apply le_antisymm
  · have := θ.le_opNorm v
    rw [hv1, mul_one, Real.norm_eq_abs] at this
    exact (le_abs_self _).trans this
  · rw [hθv]
    calc ‖θ‖ = ‖c0 θ • φ1 + c1 θ • φ2‖ := by rw [← hrepr θ]
      _ ≤ ‖c0 θ • φ1‖ + ‖c1 θ • φ2‖ := norm_add_le _ _
      _ ≤ c0 θ + c1 θ := by
        rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hθ.1,
          abs_of_pos hθ.2]
        nlinarith [hθ.1, hθ.2]

end Smooth

section Main

variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup W]
  [NormedSpace ℝ W] {g : W → V}

theorem inj
    (hrad : ∀ w ∈ extremePoints ℝ (closedBall (0 : W) 1),
      ∀ w' ∈ extremePoints ℝ (closedBall (0 : W) 1), ∀ α β : ℝ,
        ‖α • w + β • w'‖ ≤ ‖α • g w + β • g w'‖)
    {w w' : W} (hw : w ∈ extremePoints ℝ (closedBall (0 : W) 1))
    (hw' : w' ∈ extremePoints ℝ (closedBall (0 : W) 1)) (h : g w = g w') : w = w' := by
  have := hrad w hw w' hw' 1 (-1)
  rw [h, one_smul, one_smul, neg_one_smul, neg_one_smul, ← sub_eq_add_neg, ← sub_eq_add_neg,
    sub_self, norm_zero] at this
  exact sub_eq_zero.mp (norm_le_zero_iff.mp this)

theorem indep_g
    (hrad : ∀ w ∈ extremePoints ℝ (closedBall (0 : W) 1),
      ∀ w' ∈ extremePoints ℝ (closedBall (0 : W) 1), ∀ α β : ℝ,
        ‖α • w + β • w'‖ ≤ ‖α • g w + β • g w'‖)
    {u v : W} (hu : u ∈ extremePoints ℝ (closedBall (0 : W) 1))
    (hv : v ∈ extremePoints ℝ (closedBall (0 : W) 1)) (h : LinearIndependent ℝ ![u, v]) :
    LinearIndependent ℝ ![g u, g v] := by
  rw [LinearIndependent.pair_iff] at h ⊢
  intro s t hst
  apply h s t
  have := hrad u hu v hv s t
  rw [hst, norm_zero] at this
  exact norm_le_zero_iff.mp this

theorem normg (hW : Module.finrank ℝ W = 2)
    (hball : ∀ w ∈ extremePoints ℝ (closedBall (0 : W) 1), ‖g w‖ ≤ 1)
    (hrad : ∀ w ∈ extremePoints ℝ (closedBall (0 : W) 1),
      ∀ w' ∈ extremePoints ℝ (closedBall (0 : W) 1), ∀ α β : ℝ,
        ‖α • w + β • w'‖ ≤ ‖α • g w + β • g w'‖)
    {w : W} (hw : w ∈ extremePoints ℝ (closedBall (0 : W) 1)) : ‖g w‖ = 1 := by
  apply le_antisymm (hball w hw)
  have := hrad w hw w hw 1 0
  rw [one_smul, one_smul, zero_smul, zero_smul, add_zero, add_zero, norm_eq_one hW hw] at this
  exact this

/-- A functional takes the value one at only finitely many extreme points of a planar ball. -/
theorem face_finite (hW : Module.finrank ℝ W = 2) (θ : StrongDual ℝ W) :
    {u | u ∈ extremePoints ℝ (closedBall (0 : W) 1) ∧ θ u = 1}.Finite := by
  by_cases h : ∃ p ∈ extremePoints ℝ (closedBall (0 : W) 1), θ p = 1 ∧
      ∃ q ∈ extremePoints ℝ (closedBall (0 : W) 1), θ q = 1 ∧ p ≠ q
  · obtain ⟨p, hp, hθp, q, hq, hθq, hpq⟩ := h
    apply (Set.toFinite {p, q}).subset
    rintro u ⟨hu, hθu⟩
    rcases face_three hW hp hq hu hθp hθq hθu hpq with h | h
    · simp [h]
    · simp [h]
  · push Not at h
    apply Set.Subsingleton.finite
    rintro u ⟨hu, hθu⟩ u' ⟨hu', hθu'⟩
    exact h u hu hθu u' hu' hθu'

/-- Composing a functional at `w'` with the linear map through `(g w', w')` and `(g u, u)` gives a
functional at `g w'` of norm at most one. -/
theorem exists_functional (hV : Module.finrank ℝ V = 2) (hW : Module.finrank ℝ W = 2)
    (hrad : ∀ w ∈ extremePoints ℝ (closedBall (0 : W) 1),
      ∀ w' ∈ extremePoints ℝ (closedBall (0 : W) 1), ∀ α β : ℝ,
        ‖α • w + β • w'‖ ≤ ‖α • g w + β • g w'‖)
    {w' u : W} (hw' : w' ∈ extremePoints ℝ (closedBall (0 : W) 1))
    (hu : u ∈ extremePoints ℝ (closedBall (0 : W) 1)) (h1 : u ≠ w') (h2 : u ≠ -w')
    {ψ : StrongDual ℝ W} (hψ : ‖ψ‖ ≤ 1) (hψw' : ψ w' = 1) :
    ∃ φ : StrongDual ℝ V, ‖φ‖ ≤ 1 ∧ φ (g w') = 1 ∧ φ (g u) = ψ u := by
  have : FiniteDimensional ℝ V := FiniteDimensional.of_finrank_eq_succ hV
  have hind : LinearIndependent ℝ ![w', u] := indep_of_unit (norm_eq_one hW hw')
    (norm_eq_one hW hu) h1.symm (by intro h; apply h2; rw [h, neg_neg])
  have hgind := indep_g hrad hw' hu hind
  obtain ⟨B, hB1, hB2⟩ := exists_linearMap hV hgind w' u
  have hBc : ∀ v, ‖B v‖ ≤ ‖v‖ := by
    intro v
    obtain ⟨α, β, rfl⟩ := exists_coords hV hgind v
    rw [map_add, map_smul, map_smul, hB1, hB2]
    exact hrad w' hw' u hu α β
  refine ⟨ψ.comp (LinearMap.toContinuousLinearMap B), ?_, ?_, ?_⟩
  · refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun v => ?_)
    rw [ContinuousLinearMap.comp_apply, LinearMap.coe_toContinuousLinearMap', one_mul,
      Real.norm_eq_abs]
    exact (abs_le_norm hψ _).trans (hBc v)
  · rw [ContinuousLinearMap.comp_apply, LinearMap.coe_toContinuousLinearMap', hB1, hψw']
  · rw [ContinuousLinearMap.comp_apply, LinearMap.coe_toContinuousLinearMap', hB2]

/-- At an extreme point `w'` whose image is a smooth point, every norming functional of `w'`
is invariant under the linear map through `(g w₁, w₁)` and `(g w₂, w₂)`, on `g w`. -/
theorem eval_A (hV : Module.finrank ℝ V = 2) (hW : Module.finrank ℝ W = 2)
    (hrad : ∀ w ∈ extremePoints ℝ (closedBall (0 : W) 1),
      ∀ w' ∈ extremePoints ℝ (closedBall (0 : W) 1), ∀ α β : ℝ,
        ‖α • w + β • w'‖ ≤ ‖α • g w + β • g w'‖)
    {w1 w2 w w' : W} (hw1 : w1 ∈ extremePoints ℝ (closedBall (0 : W) 1))
    (hw2 : w2 ∈ extremePoints ℝ (closedBall (0 : W) 1))
    (hw : w ∈ extremePoints ℝ (closedBall (0 : W) 1))
    (hw' : w' ∈ extremePoints ℝ (closedBall (0 : W) 1))
    (hgood : ∀ φ1 φ2 : StrongDual ℝ V, ‖φ1‖ ≤ 1 → ‖φ2‖ ≤ 1 → φ1 (g w') = 1 →
      φ2 (g w') = 1 → φ1 = φ2)
    (h1 : w1 ≠ w' ∧ w1 ≠ -w') (h2 : w2 ≠ w' ∧ w2 ≠ -w') (h3 : w ≠ w' ∧ w ≠ -w')
    (hgind : LinearIndependent ℝ ![g w1, g w2]) {A : V →ₗ[ℝ] W} (hA1 : A (g w1) = w1)
    (hA2 : A (g w2) = w2) {ψ : StrongDual ℝ W} (hψ : ‖ψ‖ ≤ 1) (hψw' : ψ w' = 1) :
    ψ (A (g w)) = ψ w := by
  obtain ⟨φ1, hφ1, hφ1w', hφ1u⟩ := exists_functional hV hW hrad hw' hw1 h1.1 h1.2 hψ hψw'
  obtain ⟨φ2, hφ2, hφ2w', hφ2u⟩ := exists_functional hV hW hrad hw' hw2 h2.1 h2.2 hψ hψw'
  obtain ⟨φ3, hφ3, hφ3w', hφ3u⟩ := exists_functional hV hW hrad hw' hw h3.1 h3.2 hψ hψw'
  have e2 : φ2 = φ1 := hgood _ _ hφ2 hφ1 hφ2w' hφ1w'
  have e3 : φ3 = φ1 := hgood _ _ hφ3 hφ1 hφ3w' hφ1w'
  obtain ⟨α, β, hgw⟩ := exists_coords hV hgind (g w)
  calc ψ (A (g w)) = α * ψ w1 + β * ψ w2 := by
        rw [hgw, map_add, map_smul, map_smul, hA1, hA2, map_add, map_smul, map_smul,
          smul_eq_mul, smul_eq_mul]
    _ = α * φ1 (g w1) + β * φ1 (g w2) := by rw [hφ1u, ← hφ2u, e2]
    _ = φ1 (g w) := by rw [hgw, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
    _ = ψ w := by rw [← e3, hφ3u]

/-- Two functionals vanishing at the same nonzero vector of a plane are proportional. -/
theorem dual_dep (hW : Module.finrank ℝ W = 2) {x p : W} (hx : x ≠ 0)
    {ψ1 ψ2 : StrongDual ℝ W} (h1 : ψ1 x = 0) (h2 : ψ2 x = 0) (hp : ψ1 p = 1) :
    ∀ z, ψ2 z = ψ1 z * ψ2 p := by
  have hind : LinearIndependent ℝ ![x, p] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    have h := congrArg ψ1 hst
    simp only [map_add, map_smul, smul_eq_mul, h1, hp, mul_zero, mul_one, zero_add,
      map_zero] at h
    subst h
    rw [zero_smul, add_zero] at hst
    rcases smul_eq_zero.mp hst with h | h
    · exact ⟨h, rfl⟩
    · exact absurd h hx
  intro z
  obtain ⟨α, β, rfl⟩ := exists_coords hW hind z
  simp only [map_add, map_smul, smul_eq_mul, h1, h2, hp]
  ring

end Main

end Sol_Plasticity_Plane_exists_linearIsometryEquiv_of_radial_le_uncountable

open Sol_Plasticity_Plane_exists_linearIsometryEquiv_of_radial_le_uncountable in
theorem solution {V W : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup W] [NormedSpace ℝ W]
    (hV : Module.finrank ℝ V = 2) (hW : Module.finrank ℝ W = 2) (g : W → V)
    (hball : ∀ w ∈ Set.extremePoints ℝ (Metric.closedBall (0 : W) 1), ‖g w‖ ≤ 1)
    (hrad : ∀ w ∈ Set.extremePoints ℝ (Metric.closedBall (0 : W) 1),
      ∀ w' ∈ Set.extremePoints ℝ (Metric.closedBall (0 : W) 1), ∀ α β : ℝ,
        ‖α • w + β • w'‖ ≤ ‖α • g w + β • g w'‖)
    (hunc : ¬ (Set.extremePoints ℝ (Metric.closedBall (0 : W) 1)).Countable) :
    ∃ L : V ≃ₗᵢ[ℝ] W, ∀ w ∈ Set.extremePoints ℝ (Metric.closedBall (0 : W) 1), L (g w) = w := by
  have : FiniteDimensional ℝ V := FiniteDimensional.of_finrank_eq_succ hV
  have : FiniteDimensional ℝ W := FiniteDimensional.of_finrank_eq_succ hW
  set E := Set.extremePoints ℝ (Metric.closedBall (0 : W) 1) with hE
  have hEne : ∀ C : Set W, C.Countable → ∃ u ∈ E, u ∉ C := fun C hC => by
    by_contra h
    push Not at h
    exact hunc (hC.mono h)
  obtain ⟨w1, hw1, -⟩ := hEne ∅ Set.countable_empty
  obtain ⟨w2, hw2, hw2C⟩ := hEne {w1, -w1} (Set.toFinite _).countable
  have hind : LinearIndependent ℝ ![w1, w2] := indep_of_unit (norm_eq_one hW hw1)
    (norm_eq_one hW hw2) (fun h => hw2C (by simp [h]))
    (fun h => hw2C (by rw [h, neg_neg]; simp))
  have hgind := indep_g hrad hw1 hw2 hind
  obtain ⟨A, hA1, hA2⟩ := exists_linearMap hV hgind w1 w2
  have hA : ∀ v, ‖A v‖ ≤ ‖v‖ := by
    intro v
    obtain ⟨α, β, rfl⟩ := exists_coords hV hgind v
    rw [map_add, map_smul, map_smul, hA1, hA2]
    exact hrad w1 hw1 w2 hw2 α β
  set N := {v : V | ‖v‖ = 1 ∧ ∃ φ1 φ2 : StrongDual ℝ V, ‖φ1‖ ≤ 1 ∧ ‖φ2‖ ≤ 1 ∧ φ1 v = 1 ∧
      φ2 v = 1 ∧ φ1 ≠ φ2} with hN
  have hbad : (E ∩ g ⁻¹' N).Countable :=
    Set.MapsTo.countable_of_injOn (f := g) (t := N) (fun x hx => hx.2)
      (by intro x hx y hy h; exact inj hrad hx.1 hy.1 h) (countable_nonsmooth hV)
  have key : ∀ w ∈ E, A (g w) = w := by
    intro w hw
    by_contra hne
    have hx : A (g w) - w ≠ 0 := sub_ne_zero.mpr hne
    set C0 : Set W := (E ∩ g ⁻¹' N) ∪ {w1, -w1, w2, -w2, w, -w} with hC0def
    have hC0 : C0.Countable := hbad.union (Set.toFinite _).countable
    have hzero : ∀ w' ∈ E, w' ∉ C0 → ∀ ψ : StrongDual ℝ W, ‖ψ‖ ≤ 1 → ψ w' = 1 →
        ψ (A (g w) - w) = 0 := by
      intro w' hw' hC ψ hψ hψw'
      have hgood : ∀ φ1 φ2 : StrongDual ℝ V, ‖φ1‖ ≤ 1 → ‖φ2‖ ≤ 1 → φ1 (g w') = 1 →
          φ2 (g w') = 1 → φ1 = φ2 := by
        intro φ1 φ2 h1 h2 h3 h4
        by_contra hne'
        exact hC (Or.inl ⟨hw', normg hW hball hrad hw', φ1, φ2, h1, h2, h3, h4, hne'⟩)
      have hn : ∀ u ∈ ({w1, -w1, w2, -w2, w, -w} : Set W), u ≠ w' := by
        intro u hu h
        exact hC (Or.inr (h ▸ hu))
      have ne1 : w1 ≠ w' ∧ w1 ≠ -w' := ⟨hn w1 (by simp), fun h => hn (-w1) (by simp)
        (by rw [h, neg_neg])⟩
      have ne2 : w2 ≠ w' ∧ w2 ≠ -w' := ⟨hn w2 (by simp), fun h => hn (-w2) (by simp)
        (by rw [h, neg_neg])⟩
      have ne3 : w ≠ w' ∧ w ≠ -w' := ⟨hn w (by simp), fun h => hn (-w) (by simp)
        (by rw [h, neg_neg])⟩
      rw [map_sub, eval_A hV hW hrad hw1 hw2 hw hw' hgood ne1 ne2 ne3 hgind hA1 hA2 hψ hψw',
        sub_self]
    obtain ⟨u1, hu1, hu1C⟩ := hEne C0 hC0
    obtain ⟨ψ1, hψ1n, hψ1⟩ := exists_dual_vector ℝ u1 (by rw [norm_eq_one hW hu1]; norm_num)
    have hψ1u : ψ1 u1 = 1 := by rw [hψ1, norm_eq_one hW hu1]; rfl
    set F1 : Set W := {u | u ∈ E ∧ ψ1 u = 1} ∪ {u | u ∈ E ∧ (-ψ1) u = 1} with hF1def
    have hF1 : F1.Countable := ((face_finite hW ψ1).union (face_finite hW (-ψ1))).countable
    obtain ⟨u2, hu2, hu2C⟩ := hEne (C0 ∪ F1) (hC0.union hF1)
    obtain ⟨ψ2, hψ2n, hψ2⟩ := exists_dual_vector ℝ u2 (by rw [norm_eq_one hW hu2]; norm_num)
    have hψ2u : ψ2 u2 = 1 := by rw [hψ2, norm_eq_one hW hu2]; rfl
    have z1 := hzero u1 hu1 hu1C ψ1 hψ1n.le hψ1u
    have z2 := hzero u2 hu2 (fun h => hu2C (Or.inl h)) ψ2 hψ2n.le hψ2u
    have hdep := dual_dep hW hx z1 z2 hψ1u
    have e1 : ψ1 u2 * ψ2 u1 = 1 := by rw [← hdep, hψ2u]
    have b1 : |ψ2 u1| ≤ 1 := (abs_le_norm hψ2n.le u1).trans (norm_eq_one hW hu1).le
    have b2 : |ψ1 u2| ≤ 1 := (abs_le_norm hψ1n.le u2).trans (norm_eq_one hW hu2).le
    have habs : |ψ1 u2| = 1 := by
      have h := congrArg abs e1
      rw [abs_mul, abs_one] at h
      nlinarith [abs_nonneg (ψ1 u2), abs_nonneg (ψ2 u1)]
    rcases (abs_eq zero_le_one).mp habs with h | h
    · exact hu2C (Or.inr (Or.inl ⟨hu2, h⟩))
    · exact hu2C (Or.inr (Or.inr ⟨hu2, by rw [neg_apply, h, neg_neg]⟩))
  obtain ⟨L, hL⟩ :=
    Plasticity.Plane.exists_linearIsometryEquiv_of_contraction_of_extremePoints
      (by rw [hV, hW]) A hA g (fun w hw => ⟨hball w hw, key w hw⟩)
  exact ⟨L, fun w hw => by rw [hL]; exact key w hw⟩
