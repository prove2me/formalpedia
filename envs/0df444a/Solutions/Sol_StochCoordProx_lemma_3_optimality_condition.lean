-- Prove2me | solution 1 for StochCoordProx.lemma_3_optimality_condition
-- status  : ACCEPTED   (prove)
-- author  : @涼宮 ハルヒ
-- created : 2026-11-02T12:25:20.127211+00:00
-- url     : https://prove2.me/submissions/affe6f84-1ea0-4c17-aa31-e1b67306f771

import Definitions.Def_StochCoordProx_IsDirStationary
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Convex.Function
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Module
import Mathlib.Tactic.Ring

open Set Filter Topology
open scoped InnerProductSpace

theorem solution {m : ℕ} (θ φ : EuclideanSpace ℝ (Fin m) → ℝ)
    (D : Set (EuclideanSpace ℝ (Fin m))) (hθ : Differentiable ℝ θ) (hφ : ConvexOn ℝ D φ)
    (ystar : EuclideanSpace ℝ (Fin m)) (hystar : ystar ∈ D) :
    StochCoordProx.IsDirStationary (fun y => θ y + φ y) D ystar ↔
      ∀ y ∈ D, ⟪gradient θ ystar, y - ystar⟫_ℝ + φ y - φ ystar ≥ 0 := by
  have hlim (y : EuclideanSpace ℝ (Fin m)) :
      Tendsto (fun t : ℝ => (θ (ystar + t • (y-ystar)) - θ ystar) / t)
        (𝓝[>] 0) (𝓝 ⟪gradient θ ystar, y-ystar⟫_ℝ) := by
    have hp : HasDerivAt (fun t : ℝ => ystar + t • (y-ystar)) (y-ystar) 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (y-ystar)).const_add ystar
    have hd : HasDerivAt (fun t : ℝ => θ (ystar + t • (y-ystar)))
        ⟪gradient θ ystar, y-ystar⟫_ℝ 0 := by
      have hc := (hθ (ystar + (0 : ℝ) • (y-ystar))).hasFDerivAt.comp_hasDerivAt 0 hp
      convert! hc using 1
      simp only [zero_smul, add_zero, inner_gradient_left]
    simpa only [zero_add, zero_smul, add_zero, smul_eq_mul, div_eq_mul_inv,
      mul_comm] using hd.tendsto_slope_zero_right
  have hpath (y : EuclideanSpace ℝ (Fin m)) (hy : y ∈ D) (t : ℝ)
      (ht0 : 0 ≤ t) (ht1 : t ≤ 1) : ystar + t • (y-ystar) ∈ D := by
    have hv : ystar + t • (y-ystar) = (1-t) • ystar + t • y := by module
    rw [hv]
    exact hφ.1 hystar hy (by linarith) ht0 (by ring)
  have hpos : ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ), 0 < t := self_mem_nhdsWithin
  have hsmall : ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ), t < 1 :=
    eventually_nhdsWithin_of_eventually_nhds (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1))
  constructor
  · intro hs y hy
    by_contra hnonneg
    have hneg : ⟪gradient θ ystar, y-ystar⟫_ℝ + φ y - φ ystar < 0 := lt_of_not_ge hnonneg
    let ε : ℝ := -(⟪gradient θ ystar, y-ystar⟫_ℝ + φ y - φ ystar)/4
    have he : 0 < ε := by dsimp [ε]; linarith
    have hclose := (tendsto_order.mp (hlim y)).2
      (⟪gradient θ ystar, y-ystar⟫_ℝ + ε) (by linarith)
    have hstat := hs y hy ε he
    obtain ⟨t, hst, hcl, ht0, ht1⟩ :=
      (hstat.and (hclose.and (hpos.and hsmall))).exists
    have hc := hφ.2 hystar hy (show 0 ≤ 1-t by linarith) (le_of_lt ht0)
      (show 1-t+t=1 by ring)
    have hv : (1-t) • ystar + t • y = ystar + t • (y-ystar) := by module
    rw [hv] at hc
    simp only [smul_eq_mul] at hc
    have ht := (div_lt_iff₀ ht0).mp hcl
    have hs' := (le_div_iff₀ ht0).mp hst
    dsimp only at hs'
    have hbad : t * (⟪gradient θ ystar, y-ystar⟫_ℝ + φ y - φ ystar + 2*ε) ≥ 0 := by
      nlinarith
    have hpos := nonneg_of_mul_nonneg_right hbad ht0
    dsimp [ε] at hpos
    linarith
  · intro hs y hy ε he
    have hclose := (tendsto_order.mp (hlim y)).1
      (⟪gradient θ ystar, y-ystar⟫_ℝ - ε) (by linarith)
    filter_upwards [hclose, self_mem_nhdsWithin,
      eventually_nhdsWithin_of_eventually_nhds
        (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1))] with t hcl ht0 ht1
    have hv := hs (ystar + t • (y-ystar)) (hpath y hy t ht0.le ht1.le)
    have hsub : ystar + t • (y-ystar) - ystar = t • (y-ystar) := by abel
    rw [hsub, inner_smul_right] at hv
    apply (le_div_iff₀ ht0).mpr
    have hct := (lt_div_iff₀ ht0).mp hcl
    nlinarith

#print axioms solution
