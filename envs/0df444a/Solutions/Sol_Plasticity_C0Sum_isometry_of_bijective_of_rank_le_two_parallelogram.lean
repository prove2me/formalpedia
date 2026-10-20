-- Prove2me | solution 1 for Plasticity.C0Sum.isometry_of_bijective_of_rank_le_two.parallelogram
-- status  : ACCEPTED   (prove)
-- author  : @scanstone
-- created : 2026-10-19T19:04:04.7858+00:00
-- url     : https://prove2.me/submissions/4d219a04-1ed4-4f10-bb6f-bdbf56f42330

import Mathlib.Analysis.Convex.Extreme
import Mathlib.Analysis.Convex.KreinMilman
import Mathlib.Analysis.Convex.Strict.Extreme
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Data.Set.Card
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
A plane whose unit ball has at most four extreme points is `ℓ∞²`: by Krein–Milman the ball is
the convex hull of its extreme points, which are `±p, ±q` for independent `p, q`; in the basis
`a = (p + q) / 2`, `b = (p - q) / 2` the norm is the maximum of the absolute coordinates.
-/

namespace Sol_Plasticity_C0Sum_isometry_of_bijective_of_rank_le_two_parallelogram

open Metric Set

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem abs_add_add_abs_sub (s t : ℝ) : |s + t| + |s - t| = 2 * max |s| |t| := by
  rcases le_total |s| |t| with h | h
  · rw [max_eq_right h]
    rcases abs_cases s with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rcases abs_cases t with ⟨h3, h4⟩ | ⟨h3, h4⟩ <;>
      rcases abs_cases (s + t) with ⟨h5, h6⟩ | ⟨h5, h6⟩ <;>
      rcases abs_cases (s - t) with ⟨h7, h8⟩ | ⟨h7, h8⟩ <;> linarith
  · rw [max_eq_left h]
    rcases abs_cases s with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rcases abs_cases t with ⟨h3, h4⟩ | ⟨h3, h4⟩ <;>
      rcases abs_cases (s + t) with ⟨h5, h6⟩ | ⟨h5, h6⟩ <;>
      rcases abs_cases (s - t) with ⟨h7, h8⟩ | ⟨h7, h8⟩ <;> linarith

/-- The extreme points of the unit ball are symmetric. -/
theorem neg_mem_extremePoints {x : V} (hx : x ∈ extremePoints ℝ (closedBall (0 : V) 1)) :
    -x ∈ extremePoints ℝ (closedBall (0 : V) 1) := by
  rw [mem_extremePoints] at hx ⊢
  refine ⟨by simpa using hx.1, fun y hy z hz hseg => ?_⟩
  obtain ⟨a, b, ha, hb, hab, h⟩ := hseg
  have := hx.2 (-y) (by simpa using hy) (-z) (by simpa using hz)
    ⟨a, b, ha, hb, hab, by rw [smul_neg, smul_neg, ← neg_add, h, neg_neg]⟩
  exact ⟨by rw [← neg_neg y, this.1], by rw [← neg_neg z, this.2]⟩

theorem ne_neg_of_ne_zero {x : V} (hx : x ≠ 0) : x ≠ -x := by
  intro h
  have h2 : (2 : ℝ) • x = 0 := by
    rw [two_smul]
    calc x + x = -x + x := congrArg (· + x) h
      _ = 0 := neg_add_cancel x
  exact hx ((smul_eq_zero.1 h2).resolve_left two_ne_zero)

/-- A linear functional at most one on a set whose convex hull is the unit ball is bounded by
the norm. -/
theorem le_norm_of_le_one {X : Set V} (hX : convexHull ℝ X = closedBall (0 : V) 1)
    (ℓ : V →ₗ[ℝ] ℝ) (hℓ : ∀ x ∈ X, ℓ x ≤ 1) (v : V) : ℓ v ≤ ‖v‖ := by
  rcases eq_or_ne v 0 with rfl | hv
  · simp
  have hn : 0 < ‖v‖ := norm_pos_iff.2 hv
  have hmem : ‖v‖⁻¹ • v ∈ convexHull ℝ X := by
    rw [hX, mem_closedBall_zero_iff, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hn.ne']
  have hconv : Convex ℝ {x : V | ℓ x ≤ 1} := (convex_Iic (1 : ℝ)).linear_preimage ℓ
  have h2 : ℓ (‖v‖⁻¹ • v) ≤ 1 := convexHull_min (fun x hx => hℓ x hx) hconv hmem
  rw [map_smul, smul_eq_mul] at h2
  rwa [inv_mul_le_iff₀ hn, mul_one] at h2

end Sol_Plasticity_C0Sum_isometry_of_bijective_of_rank_le_two_parallelogram

open Sol_Plasticity_C0Sum_isometry_of_bijective_of_rank_le_two_parallelogram in
theorem solution {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (hV : Module.finrank ℝ V = 2)
    (hext : (Set.extremePoints ℝ (Metric.closedBall (0 : V) 1)).encard ≤ 4) :
    ∃ a b : V, ∀ s t : ℝ, ‖s • a + t • b‖ = max |s| |t| := by
  classical
  have : FiniteDimensional ℝ V := Module.finite_of_finrank_eq_succ hV
  have : Nontrivial V := Module.nontrivial_of_finrank_eq_succ hV
  set X := Set.extremePoints ℝ (Metric.closedBall (0 : V) 1) with hXdef
  have hXfin : X.Finite := Set.finite_of_encard_le_coe hext
  have hhull : convexHull ℝ X = Metric.closedBall (0 : V) 1 := by
    have hK : IsCompact (Metric.closedBall (0 : V) 1) := isCompact_closedBall (0 : V) 1
    have h1 := closure_convexHull_extremePoints hK (convex_closedBall (0 : V) 1)
    rwa [(hXfin.isCompact_convexHull ℝ).isClosed.closure_eq] at h1
  have hnorm : ∀ x ∈ X, ‖x‖ = 1 := fun x hx => by
    simpa using extremePoints_closedBall_subset_sphere hx
  have hXne : X.Nonempty := by
    by_contra h
    rw [Set.not_nonempty_iff_eq_empty] at h
    rw [h, convexHull_empty] at hhull
    have : (0 : V) ∈ Metric.closedBall (0 : V) 1 := Metric.mem_closedBall_self zero_le_one
    rw [← hhull] at this
    exact this
  obtain ⟨p, hp⟩ := hXne
  have hp0 : p ≠ 0 := by
    intro h; have := hnorm p hp; rw [h, norm_zero] at this; norm_num at this
  have hq : ∃ q ∈ X, q ∉ Submodule.span ℝ {p} := by
    by_contra h
    push Not at h
    have hsub : Metric.closedBall (0 : V) 1 ⊆ Submodule.span ℝ {p} := by
      rw [← hhull]; exact convexHull_min h (Submodule.convex _)
    have htop : Submodule.span ℝ {p} = ⊤ := by
      rw [eq_top_iff]
      intro v _
      rcases eq_or_ne v 0 with rfl | hv
      · exact zero_mem _
      have hn : 0 < ‖v‖ := norm_pos_iff.2 hv
      have h2 : ‖v‖⁻¹ • v ∈ Submodule.span ℝ {p} := hsub (by
        rw [mem_closedBall_zero_iff, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hn.ne'])
      have h3 := Submodule.smul_mem _ ‖v‖ h2
      rwa [smul_smul, mul_inv_cancel₀ hn.ne', one_smul] at h3
    have h1 := finrank_span_singleton (K := ℝ) hp0
    rw [htop, finrank_top, hV] at h1
    norm_num at h1
  obtain ⟨q, hqX, hqs⟩ := hq
  have hqp : ∀ c : ℝ, c • p ≠ q := fun c h =>
    hqs (h ▸ Submodule.smul_mem _ c (Submodule.mem_span_singleton_self p))
  have hq0 : q ≠ 0 := fun h => hqs (h ▸ zero_mem _)
  have hpn : p ≠ -p := ne_neg_of_ne_zero hp0
  have hqn : q ≠ -q := ne_neg_of_ne_zero hq0
  have hpq : p ≠ q := fun h => hqp 1 (by rw [one_smul, h])
  have hpq' : p ≠ -q := fun h => hqp (-1) (by rw [neg_one_smul, h, neg_neg])
  have hpq'' : -p ≠ q := fun h => hqp (-1) (by rw [neg_one_smul, h])
  have hpq''' : -p ≠ -q := fun h => hpq (neg_inj.1 h)
  -- the extreme points are exactly `±p, ±q`
  have hT : X = {p, -p, q, -q} := by
    have hsub : ({p, -p, q, -q} : Set V) ⊆ X := by
      intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact hp
      · exact neg_mem_extremePoints hp
      · exact hqX
      · exact neg_mem_extremePoints hqX
    refine (Set.Finite.eq_of_subset_of_encard_le' hXfin hsub ?_).symm
    rw [Set.encard_insert_of_notMem (by simp [hpn, hpq, hpq']),
      Set.encard_insert_of_notMem (by simp [hpq'', hpq''']),
      Set.encard_insert_of_notMem (by simp [hqn]), Set.encard_singleton]
    exact hext.trans (by norm_num)
  -- coordinates in the basis `p, q`
  have hli : LinearIndependent ℝ ![p, q] := (LinearIndependent.pair_iff' hp0).2 hqp
  let B := basisOfLinearIndependentOfCardEqFinrank hli (by simp [hV])
  have hB0 : B 0 = p := by simp [B]
  have hB1 : B 1 = q := by simp [B]
  have c00 : B.coord 0 p = 1 := by rw [← hB0, Module.Basis.coord_apply, Module.Basis.repr_self]; simp
  have c01 : B.coord 0 q = 0 := by rw [← hB1, Module.Basis.coord_apply, Module.Basis.repr_self]; simp
  have c10 : B.coord 1 p = 0 := by rw [← hB0, Module.Basis.coord_apply, Module.Basis.repr_self]; simp
  have c11 : B.coord 1 q = 1 := by rw [← hB1, Module.Basis.coord_apply, Module.Basis.repr_self]; simp
  set φ : V →ₗ[ℝ] ℝ := B.coord 0 + B.coord 1 with hφ
  set ψ : V →ₗ[ℝ] ℝ := B.coord 0 - B.coord 1 with hψ
  have φp : φ p = 1 := by simp [hφ, c00, c10]
  have φq : φ q = 1 := by simp [hφ, c01, c11]
  have ψp : ψ p = 1 := by simp [hψ, c00, c10]
  have ψq : ψ q = -1 := by simp [hψ, c01, c11]
  have hbound : ∀ ℓ : V →ₗ[ℝ] ℝ, |ℓ p| ≤ 1 → |ℓ q| ≤ 1 → ∀ v, ℓ v ≤ ‖v‖ := by
    intro ℓ h1 h2 v
    refine le_norm_of_le_one hhull ℓ ?_ v
    rw [hT]
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rw [abs_le] at h1 h2
    rcases hx with rfl | rfl | rfl | rfl <;> (try simp only [map_neg]) <;> linarith
  refine ⟨(1 / 2 : ℝ) • (p + q), (1 / 2 : ℝ) • (p - q), fun s t => le_antisymm ?_ ?_⟩
  · have e : s • ((1 / 2 : ℝ) • (p + q)) + t • ((1 / 2 : ℝ) • (p - q)) =
        ((s + t) / 2) • p + ((s - t) / 2) • q := by module
    rw [e]
    calc ‖((s + t) / 2) • p + ((s - t) / 2) • q‖
        ≤ ‖((s + t) / 2) • p‖ + ‖((s - t) / 2) • q‖ := norm_add_le _ _
      _ = (|s + t| + |s - t|) / 2 := by
          rw [norm_smul, norm_smul, hnorm p hp, hnorm q hqX, Real.norm_eq_abs, Real.norm_eq_abs,
            abs_div, abs_div, abs_two]
          ring
      _ = max |s| |t| := by rw [abs_add_add_abs_sub]; ring
  · set v := s • ((1 / 2 : ℝ) • (p + q)) + t • ((1 / 2 : ℝ) • (p - q))
    have hφv : φ v = s := by simp [v, φp, φq]; ring
    have hψv : ψ v = t := by simp [v, ψp, ψq]; ring
    have h1 := hbound φ (by simp [φp]) (by simp [φq]) v
    have h2 := hbound (-φ) (by simp [φp]) (by simp [φq]) v
    have h3 := hbound ψ (by simp [ψp]) (by simp [ψq]) v
    have h4 := hbound (-ψ) (by simp [ψp]) (by simp [ψq]) v
    simp only [LinearMap.neg_apply, hφv, hψv] at h1 h2 h3 h4
    exact max_le (abs_le.2 ⟨by linarith, h1⟩) (abs_le.2 ⟨by linarith, h3⟩)
