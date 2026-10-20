-- Prove2me | solution 1 for Plasticity.Plane.exists_linearIsometryEquiv_of_radial_le_corner
-- status  : ACCEPTED   (prove)
-- author  : @scanstone
-- created : 2026-10-19T19:03:46.033672+00:00
-- url     : https://prove2.me/submissions/50e00e55-39ac-4985-92c2-00001ae1d991

import Mathlib.Analysis.Convex.Extreme
import Mathlib.Analysis.Convex.Strict.Extreme
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.Module.HahnBanach
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Operator.LinearIsometry
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Tactic.Module
import Mathlib.Tactic.LinearCombination
import Theorems.Thm_Plasticity_Plane_exists_linearIsometryEquiv_of_contraction_of_extremePoints

namespace Sol_Plasticity_Plane_exists_linearIsometryEquiv_of_radial_le_corner

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


section Corner

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

theorem neg_inj
    (hrad : ∀ w ∈ extremePoints ℝ (closedBall (0 : W) 1),
      ∀ w' ∈ extremePoints ℝ (closedBall (0 : W) 1), ∀ α β : ℝ,
        ‖α • w + β • w'‖ ≤ ‖α • g w + β • g w'‖)
    {w w' : W} (hw : w ∈ extremePoints ℝ (closedBall (0 : W) 1))
    (hw' : w' ∈ extremePoints ℝ (closedBall (0 : W) 1)) (h : g w = -g w') : w = -w' := by
  have := hrad w hw w' hw' 1 1
  rw [h, one_smul, one_smul, one_smul, one_smul, neg_add_cancel, norm_zero] at this
  exact eq_neg_of_add_eq_zero_left (norm_le_zero_iff.mp this)

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

theorem constraint (hV : Module.finrank ℝ V = 2)
    (hext : Set.MapsTo g (extremePoints ℝ (closedBall (0 : W) 1))
      (extremePoints ℝ (closedBall (0 : V) 1)))
    (hrad : ∀ w ∈ extremePoints ℝ (closedBall (0 : W) 1),
      ∀ w' ∈ extremePoints ℝ (closedBall (0 : W) 1), ∀ α β : ℝ,
        ‖α • w + β • w'‖ ≤ ‖α • g w + β • g w'‖)
    {u v e : W} (hu : u ∈ extremePoints ℝ (closedBall (0 : W) 1))
    (hv : v ∈ extremePoints ℝ (closedBall (0 : W) 1))
    (he : e ∈ extremePoints ℝ (closedBall (0 : W) 1)) {α β γ : ℝ}
    (h : α • g u + β • g v = γ • g e) : ‖α • u + β • v‖ ≤ |γ| := by
  calc ‖α • u + β • v‖ ≤ ‖α • g u + β • g v‖ := hrad u hu v hv α β
    _ = |γ| := by rw [h, norm_smul, norm_eq_one hV (hext he), Real.norm_eq_abs, mul_one]

/-- Cone lemma: no extreme point of `W` is carried by `g` strictly inside the cone over the
image of an edge; on the boundary rays it is an endpoint. -/
theorem cone (hV : Module.finrank ℝ V = 2)
    (hext : Set.MapsTo g (extremePoints ℝ (closedBall (0 : W) 1))
      (extremePoints ℝ (closedBall (0 : V) 1)))
    (hrad : ∀ w ∈ extremePoints ℝ (closedBall (0 : W) 1),
      ∀ w' ∈ extremePoints ℝ (closedBall (0 : W) 1), ∀ α β : ℝ,
        ‖α • w + β • w'‖ ≤ ‖α • g w + β • g w'‖)
    {e1 e2 w : W} (he1 : e1 ∈ extremePoints ℝ (closedBall (0 : W) 1))
    (he2 : e2 ∈ extremePoints ℝ (closedBall (0 : W) 1))
    (hw : w ∈ extremePoints ℝ (closedBall (0 : W) 1)) (h12 : e1 ≠ e2)
    {θ : StrongDual ℝ W} (hθ : ‖θ‖ ≤ 1) (hθ1 : θ e1 = 1) (hθ2 : θ e2 = 1)
    {ε α β : ℝ} (hε : ε = 1 ∨ ε = -1) (hα : 0 ≤ α) (hβ : 0 ≤ β)
    (hgw : g w = ε • (α • g e1 + β • g e2)) :
    (w = ε • e1 ∧ g w = ε • g e1) ∨ (w = ε • e2 ∧ g w = ε • g e2) := by
  have hεε : ε * ε = 1 := by rcases hε with rfl | rfl <;> norm_num
  have hp : α • g e1 + β • g e2 = ε • g w := by rw [hgw, smul_smul, hεε, one_smul]
  have hpn : ‖α • g e1 + β • g e2‖ = 1 := by
    rw [hp, norm_smul, norm_eq_one hV (hext hw), mul_one]
    rcases hε with rfl | rfl <;> norm_num
  have hle : 1 ≤ α + β := by
    calc (1 : ℝ) = ‖α • g e1 + β • g e2‖ := hpn.symm
      _ ≤ ‖α • g e1‖ + ‖β • g e2‖ := norm_add_le _ _
      _ = α + β := by
        rw [norm_smul, norm_smul, norm_eq_one hV (hext he1), norm_eq_one hV (hext he2),
          Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hα, abs_of_nonneg hβ, mul_one,
          mul_one]
  have hge : α + β ≤ 1 := by
    have h1 := hrad e1 he1 e2 he2 α β
    have h2 := le_norm hθ (α • e1 + β • e2)
    simp only [map_add, map_smul, smul_eq_mul, hθ1, hθ2, mul_one] at h2
    linarith
  have hsum : α + β = 1 := le_antisymm hge hle
  have hpF : α • g e1 + β • g e2 ∈ extremePoints ℝ (closedBall (0 : V) 1) := by
    rw [hp]
    rcases hε with rfl | rfl
    · rw [one_smul]; exact hext hw
    · rw [neg_one_smul]; exact neg_mem (hext hw)
  have hne : g e1 ≠ g e2 := fun h => h12 (inj hrad he1 he2 h)
  rcases collinear_ext (hext he1) (hext he2) hpF hne hsum rfl with h | h
  · left
    have hg : g w = ε • g e1 := by rw [hgw, h]
    refine ⟨?_, hg⟩
    rcases hε with rfl | rfl
    · rw [one_smul] at hg ⊢; exact inj hrad hw he1 hg
    · rw [neg_one_smul] at hg ⊢; exact neg_inj hrad hw he1 hg
  · right
    have hg : g w = ε • g e2 := by rw [hgw, h]
    refine ⟨?_, hg⟩
    rcases hε with rfl | rfl
    · rw [one_smul] at hg ⊢; exact inj hrad hw he2 hg
    · rw [neg_one_smul] at hg ⊢; exact neg_inj hrad hw he2 hg


/-- The step along two adjacent edges `[a, b]` and `[b, c]`: the linear map through
`(g a, a)` and `(g b, b)` also sends `g c` to `c`, and `g c` has a negative `g a`-coordinate. -/
theorem step (hV : Module.finrank ℝ V = 2) (hW : Module.finrank ℝ W = 2)
    (hext : Set.MapsTo g (extremePoints ℝ (closedBall (0 : W) 1))
      (extremePoints ℝ (closedBall (0 : V) 1)))
    (hrad : ∀ w ∈ extremePoints ℝ (closedBall (0 : W) 1),
      ∀ w' ∈ extremePoints ℝ (closedBall (0 : W) 1), ∀ α β : ℝ,
        ‖α • w + β • w'‖ ≤ ‖α • g w + β • g w'‖)
    {a b c : W} (ha : a ∈ extremePoints ℝ (closedBall (0 : W) 1))
    (hb : b ∈ extremePoints ℝ (closedBall (0 : W) 1))
    (hc : c ∈ extremePoints ℝ (closedBall (0 : W) 1)) (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c)
    {χ ψ : StrongDual ℝ W} (hχ : ‖χ‖ ≤ 1) (hψ : ‖ψ‖ ≤ 1) (hχa : χ a = 1) (hχb : χ b = 1)
    (hψb : ψ b = 1) (hψc : ψ c = 1) (hgab : LinearIndependent ℝ ![g a, g b])
    {A : V →ₗ[ℝ] W} (hAa : A (g a) = a) (hAb : A (g b) = b) :
    A (g c) = c ∧ ∃ σ κ : ℝ, g c = σ • g a + κ • g b ∧ σ < 0 := by
  have hab' : LinearIndependent ℝ ![a, b] := indep_of_unit (norm_eq_one hW ha)
    (norm_eq_one hW hb) hab (by intro h; rw [h, map_neg] at hχa; linarith)
  obtain ⟨σ, κ, hgc⟩ := exists_coords hV hgab (g c)
  have hAc : A (g c) = σ • a + κ • b := by rw [hgc, map_add, map_smul, map_smul, hAa, hAb]
  obtain ⟨σ', κ', hc'⟩ := exists_coords hW hab' c
  have hψa : ψ a < 1 := by
    have h1 := le_norm hψ a
    rw [norm_eq_one hW ha] at h1
    rcases lt_or_eq_of_le h1 with h | h
    · exact h
    · exfalso
      rcases face_three hW hb hc ha hψb hψc h hbc with h' | h'
      · exact hab h'
      · exact hac h'
  have hχc : χ c < 1 := by
    have h1 := le_norm hχ c
    rw [norm_eq_one hW hc] at h1
    rcases lt_or_eq_of_le h1 with h | h
    · exact h
    · exfalso
      rcases face_three hW ha hb hc hχa hχb h hab with h' | h'
      · exact hac h'.symm
      · exact hbc h'.symm
  have hsc : χ c = σ' + κ' := by
    rw [hc']; simp only [map_add, map_smul, smul_eq_mul, hχa, hχb, mul_one]
  have hψc' : σ' * ψ a + κ' = 1 := by
    have := congrArg ψ hc'
    simp only [map_add, map_smul, smul_eq_mul, hψb, hψc, mul_one] at this
    linarith
  by_cases h1 : 0 ≤ σ ∧ 0 ≤ κ
  · exfalso
    rcases cone hV hext hrad ha hb hc hab hχ hχa hχb (Or.inl rfl) h1.1 h1.2
      (by rw [one_smul]; exact hgc) with h | h
    · exact hac (by rw [h.1, one_smul])
    · exact hbc (by rw [h.1, one_smul])
  by_cases h2 : σ ≤ 0 ∧ κ ≤ 0
  · rcases cone hV hext hrad ha hb hc hab hχ hχa hχb (Or.inr rfl) (neg_nonneg.mpr h2.1)
      (neg_nonneg.mpr h2.2) (by rw [hgc]; module) with h | h
    · rw [neg_one_smul, neg_one_smul] at h
      have hco := coords_unique hgab
        (show σ • g a + κ • g b = (-1 : ℝ) • g a + (0 : ℝ) • g b by rw [← hgc, h.2]; module)
      refine ⟨by rw [hAc, hco.1, hco.2, h.1]; module, σ, κ, hgc, by linarith [hco.1]⟩
    · exfalso
      rw [neg_one_smul] at h
      rw [h.1, map_neg, hψb] at hψc
      linarith
  push Not at h1 h2
  have hσ0 : σ ≠ 0 := by
    intro h
    rw [h] at h1 h2
    linarith [h1 le_rfl, h2 le_rfl]
  rcases lt_or_gt_of_ne hσ0 with hσ | hσ
  · -- the main case `σ < 0 < κ`
    have hκ : 0 < κ := h2 hσ.le
    have c1 := constraint hV hext hrad hc hb ha (α := 1) (β := -κ) (γ := σ)
      (by rw [hgc]; module)
    have c2 := constraint hV hext hrad hc ha hb (α := 1) (β := -σ) (γ := κ)
      (by rw [hgc]; module)
    have c3 := constraint hV hext hrad ha hb hc (α := σ) (β := κ) (γ := 1)
      (by rw [hgc, one_smul])
    have e1 := abs_le_norm hχ ((1 : ℝ) • c + (-κ) • b)
    have e2 := abs_le_norm hψ ((1 : ℝ) • c + (-σ) • a)
    have e3 := le_norm hψ (σ • a + κ • b)
    simp only [map_add, map_smul, smul_eq_mul, hχb, hψc, hψb, mul_one, one_mul] at e1 e2 e3
    rw [abs_of_neg hσ] at c1
    rw [abs_of_pos hκ] at c2
    rw [abs_one] at c3
    have e1' := (abs_le.mp (e1.trans c1)).1
    have e2' := (abs_le.mp (e2.trans c2)).2
    have e3' := e3.trans c3
    have ht : σ * ψ a + κ = 1 := by nlinarith
    have hσ'σ : σ ≤ σ' := by
      by_contra hlt
      push Not at hlt
      have : (σ' - σ) * (1 - ψ a) < 0 := mul_neg_of_neg_of_pos (by linarith) (by linarith)
      nlinarith
    have hσ'0 : σ' < 0 := by
      by_contra hle
      push Not at hle
      have : 0 ≤ σ' * (1 - ψ a) := mul_nonneg hle (by linarith)
      nlinarith
    rcases eq_or_lt_of_le hσ'σ with heq | hlt
    · subst heq
      have hκκ : κ = κ' := by linarith
      subst hκκ
      exact ⟨by rw [hAc, hc'], σ, κ, hgc, hσ⟩
    · exfalso
      have hq : σ • a + κ • b ∈ closedBall (0 : W) 1 := by
        rw [mem_closedBall, dist_zero_right]; exact c3
      have hr0 : 0 < σ' / σ := div_pos_of_neg_of_neg hσ'0 hσ
      have hr1 : σ' / σ < 1 := (div_lt_one_of_neg hσ).mpr hlt
      have hseg : c ∈ openSegment ℝ (σ • a + κ • b) b := by
        refine ⟨σ' / σ, 1 - σ' / σ, hr0, by linarith, by ring, ?_⟩
        have f1 : σ' / σ * σ = σ' := div_mul_cancel₀ _ hσ0
        have f2 : σ' / σ * κ + (1 - σ' / σ) = κ' := by
          have hk : κ = 1 - σ * ψ a := by linarith
          have hk' : κ' = 1 - σ' * ψ a := by linarith
          rw [hk, hk']
          field_simp
          ring
        rw [hc']
        linear_combination (norm := module) f1 • a + f2 • b
      have := (mem_extremePoints.mp hc).2 _ hq b hb.1 hseg
      exact hbc this.2
  · -- the case `κ < 0 < σ` is impossible
    exfalso
    have hκ : κ < 0 := h1 hσ.le
    have c1 := constraint hV hext hrad hc hb ha (α := 1) (β := -κ) (γ := σ)
      (by rw [hgc]; module)
    have c3 := constraint hV hext hrad ha hb hc (α := σ) (β := κ) (γ := 1)
      (by rw [hgc, one_smul])
    have e1 := abs_le_norm hψ ((1 : ℝ) • c + (-κ) • b)
    have e3 := le_norm hχ (σ • a + κ • b)
    simp only [map_add, map_smul, smul_eq_mul, hχa, hχb, hψc, hψb, mul_one] at e1 e3
    rw [abs_of_pos hσ] at c1
    rw [abs_one] at c3
    have e1' := (abs_le.mp (e1.trans c1)).2
    have e3' := e3.trans c3
    have hsum : σ + κ = 1 := by linarith
    have hne : g a ≠ g b := fun h => hab (inj hrad ha hb h)
    rcases collinear_ext (hext ha) (hext hb) (hext hc) hne hsum hgc with h | h
    · exact hac (inj hrad hc ha h).symm
    · exact hbc (inj hrad hc hb h).symm


/-- Pinning in the sector between `g b` and `-g a`. -/
theorem sector (hV : Module.finrank ℝ V = 2) (hW : Module.finrank ℝ W = 2)
    (hext : Set.MapsTo g (extremePoints ℝ (closedBall (0 : W) 1))
      (extremePoints ℝ (closedBall (0 : V) 1)))
    (hrad : ∀ w ∈ extremePoints ℝ (closedBall (0 : W) 1),
      ∀ w' ∈ extremePoints ℝ (closedBall (0 : W) 1), ∀ α β : ℝ,
        ‖α • w + β • w'‖ ≤ ‖α • g w + β • g w'‖)
    {a b c w : W} (ha : a ∈ extremePoints ℝ (closedBall (0 : W) 1))
    (hb : b ∈ extremePoints ℝ (closedBall (0 : W) 1))
    (hc : c ∈ extremePoints ℝ (closedBall (0 : W) 1))
    (hw : w ∈ extremePoints ℝ (closedBall (0 : W) 1)) (hbc : b ≠ c)
    {χ ψ : StrongDual ℝ W} (hχ : ‖χ‖ ≤ 1) (hψ : ‖ψ‖ ≤ 1) (hχa : χ a = 1) (hχb : χ b = 1)
    (hψb : ψ b = 1) (hψc : ψ c = 1) (hψa : ψ a < 1)
    {A : V →ₗ[ℝ] W} (hAa : A (g a) = a) (hAb : A (g b) = b) (hAc : A (g c) = c)
    {σ κ : ℝ} (hgc : g c = σ • g a + κ • g b) (hσ : σ < 0)
    {l m : ℝ} (hgw : g w = l • g a + m • g b) (hl : l < 0) (hm : 0 < m) : A (g w) = w := by
  have hc' : c = σ • a + κ • b := by rw [← hAc, hgc, map_add, map_smul, map_smul, hAa, hAb]
  have hκ : κ = 1 - σ * ψ a := by
    have := congrArg ψ hc'
    simp only [map_add, map_smul, smul_eq_mul, hψb, hψc, mul_one] at this
    linarith
  have hAw : A (g w) = l • a + m • b := by rw [hgw, map_add, map_smul, map_smul, hAa, hAb]
  have hab : a ≠ b := by intro h; rw [h, hψb] at hψa; linarith
  have hab' : LinearIndependent ℝ ![a, b] := indep_of_unit (norm_eq_one hW ha)
    (norm_eq_one hW hb) hab (by intro h; rw [h, map_neg] at hχa; linarith)
  obtain ⟨ω1, ω2, hw'⟩ := exists_coords hW hab' w
  have hχw : χ w = ω1 + ω2 := by
    rw [hw']; simp only [map_add, map_smul, smul_eq_mul, hχa, hχb, mul_one]
  have hψw : ψ w = ω1 * ψ a + ω2 := by
    rw [hw']; simp only [map_add, map_smul, smul_eq_mul, hψb, mul_one]
  have hσ0 : σ ≠ 0 := hσ.ne
  by_cases hΔ : 0 ≤ l * κ - σ * m
  · -- `g w` lies in the closed cone over `g b` and `g c`
    have f1 : l / σ * σ = l := div_mul_cancel₀ _ hσ0
    have f2 : -(l * κ - σ * m) / σ + l / σ * κ = m := by field_simp; ring
    rcases cone hV hext hrad hb hc hw hbc hψ hψb hψc (Or.inl rfl)
      (α := -(l * κ - σ * m) / σ) (β := l / σ)
      (div_nonneg_of_nonpos (by linarith) hσ.le) (div_pos_of_neg_of_neg hl hσ).le (by
        rw [one_smul, hgw, hgc]
        linear_combination (norm := module) -(f1 • g a) - f2 • g b) with h | h
    · rw [h.2, one_smul, hAb, h.1, one_smul]
    · rw [h.2, one_smul, hAc, h.1, one_smul]
  · push Not at hΔ
    have c1 := constraint hV hext hrad hw hb ha (α := 1) (β := -m) (γ := l)
      (by rw [hgw]; module)
    have c2 := constraint hV hext hrad hw hb hc (α := σ) (β := l * κ - σ * m) (γ := l)
      (by rw [hgw, hgc]; module)
    have c3 := constraint hV hext hrad hw ha hb (α := 1) (β := -l) (γ := m)
      (by rw [hgw]; module)
    have c4 := constraint hV hext hrad hc hw hb (α := l) (β := -σ) (γ := l * κ - σ * m)
      (by rw [hgw, hgc]; module)
    have e1 := abs_le_norm hχ ((1 : ℝ) • w + (-m) • b)
    have e2 := abs_le_norm hψ (σ • w + (l * κ - σ * m) • b)
    have e3 := abs_le_norm hχ ((1 : ℝ) • w + (-l) • a)
    have e3' := abs_le_norm hψ ((1 : ℝ) • w + (-l) • a)
    have e4 := abs_le_norm hψ (l • c + (-σ) • w)
    simp only [map_add, map_smul, smul_eq_mul, hχa, hχb, hψb, hψc, mul_one, one_mul]
      at e1 e2 e3 e3' e4
    rw [abs_of_neg hl] at c1 c2
    rw [abs_of_pos hm] at c3
    rw [abs_of_neg hΔ] at c4
    have i1 := (abs_le.mp (e1.trans c1)).1
    have i2 := (abs_le.mp (e2.trans c2)).1
    have i3 := (abs_le.mp (e3.trans c3)).2
    have i3' := (abs_le.mp (e3'.trans c3)).2
    have i4 := (abs_le.mp (e4.trans c4)).1
    rw [hχw] at i1 i3
    rw [hψw] at i2 i3' i4
    rw [hκ] at i2 i4
    have hX : ω1 + ω2 = l + m := by linarith
    have hY1 : 0 ≤ σ * (ω1 * ψ a + ω2 - l * ψ a - m) := by linarith
    have hY2 : σ * (ω1 * ψ a + ω2 - l * ψ a - m) ≤ 0 := by linarith
    have hY : ω1 * ψ a + ω2 - l * ψ a - m = 0 := by
      rcases mul_eq_zero.mp (le_antisymm hY2 hY1) with h | h
      · exact absurd h hσ0
      · exact h
    have hω : (ω1 - l) * (1 - ψ a) = 0 := by linarith
    have hω1 : ω1 = l := by
      rcases mul_eq_zero.mp hω with h | h
      · linarith
      · linarith
    have hω2 : ω2 = m := by linarith
    rw [hAw, hw', hω1, hω2]


/-- Every extreme point is fixed by the linear map through `(g a, a)` and `(g b, b)`. -/
theorem fixes_all (hV : Module.finrank ℝ V = 2) (hW : Module.finrank ℝ W = 2)
    (hext : Set.MapsTo g (extremePoints ℝ (closedBall (0 : W) 1))
      (extremePoints ℝ (closedBall (0 : V) 1)))
    (hrad : ∀ w ∈ extremePoints ℝ (closedBall (0 : W) 1),
      ∀ w' ∈ extremePoints ℝ (closedBall (0 : W) 1), ∀ α β : ℝ,
        ‖α • w + β • w'‖ ≤ ‖α • g w + β • g w'‖)
    {a b c : W} (ha : a ∈ extremePoints ℝ (closedBall (0 : W) 1))
    (hb : b ∈ extremePoints ℝ (closedBall (0 : W) 1))
    (hc : c ∈ extremePoints ℝ (closedBall (0 : W) 1)) (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c)
    {χ ψ : StrongDual ℝ W} (hχ : ‖χ‖ ≤ 1) (hψ : ‖ψ‖ ≤ 1) (hχa : χ a = 1) (hχb : χ b = 1)
    (hψb : ψ b = 1) (hψc : ψ c = 1) (hgab : LinearIndependent ℝ ![g a, g b])
    {A : V →ₗ[ℝ] W} (hAa : A (g a) = a) (hAb : A (g b) = b) :
    ∀ w ∈ extremePoints ℝ (closedBall (0 : W) 1), A (g w) = w := by
  obtain ⟨hAc, σ, κ, hgc, hσ⟩ :=
    step hV hW hext hrad ha hb hc hab hbc hac hχ hψ hχa hχb hψb hψc hgab hAa hAb
  have hψa : ψ a < 1 := lt_one_of_face hW hψ hb hc ha hψb hψc hbc hab hac
  have hχc : χ c < 1 := lt_one_of_face hW hχ ha hb hc hχa hχb hab hac.symm hbc.symm
  have hσ0 : σ ≠ 0 := hσ.ne
  intro w hw
  obtain ⟨l, m, hgw⟩ := exists_coords hV hgab (g w)
  by_cases h1 : 0 ≤ l ∧ 0 ≤ m
  · rcases cone hV hext hrad ha hb hw hab hχ hχa hχb (Or.inl rfl) h1.1 h1.2
      (by rw [one_smul]; exact hgw) with h | h
    · rw [h.2, one_smul, hAa, h.1, one_smul]
    · rw [h.2, one_smul, hAb, h.1, one_smul]
  by_cases h2 : l ≤ 0 ∧ m ≤ 0
  · rcases cone hV hext hrad ha hb hw hab hχ hχa hχb (Or.inr rfl) (neg_nonneg.mpr h2.1)
      (neg_nonneg.mpr h2.2) (by rw [hgw]; module) with h | h
    · rw [h.2, neg_one_smul, map_neg, hAa, h.1, neg_one_smul]
    · rw [h.2, neg_one_smul, map_neg, hAb, h.1, neg_one_smul]
  push Not at h1 h2
  have hl0 : l ≠ 0 := by
    intro h
    rw [h] at h1 h2
    linarith [h1 le_rfl, h2 le_rfl]
  rcases lt_or_gt_of_ne hl0 with hl | hl
  · exact sector hV hW hext hrad ha hb hc hw hbc hχ hψ hχa hχb hψb hψc hψa hAa hAb hAc hgc hσ
      hgw hl (h2 hl.le)
  · have hm : m < 0 := h1 hl.le
    by_cases hΔ : m * σ - l * κ < 0
    · -- the sector lemma for the reversed triple `(c, b, a)`
      have f1 : 1 / σ * σ = 1 := by field_simp
      have f2 : 1 / σ * κ + -κ / σ = 0 := by field_simp; ring
      have f3 : l / σ * σ = l := div_mul_cancel₀ _ hσ0
      have f4 : l / σ * κ + (m * σ - l * κ) / σ = m := by field_simp; ring
      exact sector hV hW hext hrad hc hb ha hw hab.symm hψ hχ hψc hψb hχb hχa hχc hAc hAb hAa
        (σ := 1 / σ) (κ := -κ / σ)
        (by rw [hgc]; linear_combination (norm := module) -(f1 • g a) - f2 • g b)
        (div_neg_of_pos_of_neg one_pos hσ)
        (l := l / σ) (m := (m * σ - l * κ) / σ)
        (by rw [hgw, hgc]; linear_combination (norm := module) -(f3 • g a) - f4 • g b)
        (div_neg_of_pos_of_neg hl hσ) (div_pos_of_neg_of_neg hΔ hσ)
    · push Not at hΔ
      have f3 : -(-l / σ) * σ = l := by field_simp
      have f4 : -(-(m * σ - l * κ) / σ) + -(-l / σ) * κ = m := by field_simp; ring
      rcases cone hV hext hrad hb hc hw hbc hψ hψb hψc (Or.inr rfl)
        (α := -(m * σ - l * κ) / σ) (β := -l / σ)
        (div_nonneg_of_nonpos (by linarith) hσ.le)
        (div_nonneg_of_nonpos (by linarith) hσ.le)
        (by rw [hgw, hgc]; linear_combination (norm := module) -(f3 • g a) - f4 • g b)
        with h | h
      · rw [h.2, neg_one_smul, map_neg, hAb, h.1, neg_one_smul]
      · rw [h.2, neg_one_smul, map_neg, hAc, h.1, neg_one_smul]

end Corner

end Sol_Plasticity_Plane_exists_linearIsometryEquiv_of_radial_le_corner

open Sol_Plasticity_Plane_exists_linearIsometryEquiv_of_radial_le_corner in
theorem solution {V W : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup W] [NormedSpace ℝ W]
    (hV : Module.finrank ℝ V = 2) (hW : Module.finrank ℝ W = 2) (g : W → V)
    (hext : Set.MapsTo g (Set.extremePoints ℝ (Metric.closedBall (0 : W) 1))
      (Set.extremePoints ℝ (Metric.closedBall (0 : V) 1)))
    (hrad : ∀ w ∈ Set.extremePoints ℝ (Metric.closedBall (0 : W) 1),
      ∀ w' ∈ Set.extremePoints ℝ (Metric.closedBall (0 : W) 1), ∀ α β : ℝ,
        ‖α • w + β • w'‖ ≤ ‖α • g w + β • g w'‖)
    {a b c : W} (ha : a ∈ Set.extremePoints ℝ (Metric.closedBall (0 : W) 1))
    (hb : b ∈ Set.extremePoints ℝ (Metric.closedBall (0 : W) 1))
    (hc : c ∈ Set.extremePoints ℝ (Metric.closedBall (0 : W) 1))
    (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c) (hab2 : ‖a + b‖ = 2) (hbc2 : ‖b + c‖ = 2) :
    ∃ L : V ≃ₗᵢ[ℝ] W, ∀ w ∈ Set.extremePoints ℝ (Metric.closedBall (0 : W) 1), L (g w) = w := by
  have : FiniteDimensional ℝ V := FiniteDimensional.of_finrank_eq_succ hV
  have : FiniteDimensional ℝ W := FiniteDimensional.of_finrank_eq_succ hW
  obtain ⟨χ, hχ, hχa, hχb⟩ := exists_edge_functional (norm_eq_one hW ha).le
    (norm_eq_one hW hb).le hab2
  obtain ⟨ψ, hψ, hψb, hψc⟩ := exists_edge_functional (norm_eq_one hW hb).le
    (norm_eq_one hW hc).le hbc2
  have hab' : LinearIndependent ℝ ![a, b] := indep_of_unit (norm_eq_one hW ha)
    (norm_eq_one hW hb) hab (by intro h; rw [h, map_neg] at hχa; linarith)
  have hgab := indep_g hrad ha hb hab'
  obtain ⟨A, hAa, hAb⟩ := exists_linearMap hV hgab a b
  have hA : ∀ v, ‖A v‖ ≤ ‖v‖ := by
    intro v
    obtain ⟨α, β, rfl⟩ := exists_coords hV hgab v
    rw [map_add, map_smul, map_smul, hAa, hAb]
    exact hrad a ha b hb α β
  have key := fixes_all hV hW hext hrad ha hb hc hab hbc hac hχ hψ hχa hχb hψb hψc hgab hAa hAb
  obtain ⟨L, hL⟩ :=
    Plasticity.Plane.exists_linearIsometryEquiv_of_contraction_of_extremePoints
      (by rw [hV, hW]) A hA g (fun w hw => ⟨(norm_eq_one hV (hext hw)).le, key w hw⟩)
  exact ⟨L, fun w hw => by rw [hL]; exact key w hw⟩
