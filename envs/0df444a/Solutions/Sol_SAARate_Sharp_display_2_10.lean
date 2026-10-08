-- Prove2me | solution 1 for SAARate.Sharp.display_2_10
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-07T04:14:43.311855+00:00
-- url     : https://prove2.me/submissions/5e4dc1ef-23d5-424c-892c-05885ab2142d

import Mathlib
import Definitions.Def_SAARate_Sharp_Setting

open SAARate.Sharp Filter Set
open scoped Topology

theorem line_convex {m : ℕ} (g : E m → ℝ) (hg : ConvexOn ℝ univ g) (x d : E m) :
    ConvexOn ℝ univ (fun t : ℝ => g (x + t • d)) := by
  refine ⟨convex_univ, ?_⟩
  intro a _ b _ u v hu hv huv
  have hh := hg.2 (mem_univ (x + a • d)) (mem_univ (x + b • d)) hu hv huv
  have he : u • (x + a • d) + v • (x + b • d) = x + (u * a + v * b) • d := by
    rw [smul_add, smul_add, smul_smul, smul_smul]
    calc
      u • x + (u * a) • d + (v • x + (v * b) • d) =
          (u + v) • x + (u * a + v * b) • d := by module
      _ = x + (u * a + v * b) • d := by rw [huv, one_smul]
  rw [he] at hh
  simpa only [smul_eq_mul] using hh

theorem quotient_tendsto {m : ℕ} (g : E m → ℝ) (hg : ConvexOn ℝ univ g) (x d : E m) :
    Tendsto (fun t : ℝ => (g (x + t • d) - g x) / t)
      (𝓝[>] 0) (𝓝 (dirDeriv g x d)) := by
  let f : ℝ → ℝ := fun t => g (x + t • d)
  have hd := (line_convex g hg x d).hasDerivWithinAt_rightDeriv_of_mem_interior
    (x := (0 : ℝ)) (by simp)
  have hl := (hasDerivWithinAt_iff_tendsto_slope' (show (0 : ℝ) ∉ Ioi 0 by simp)).mp hd
  have hl' : Tendsto (fun t : ℝ => (g (x + t • d) - g x) / t)
      (𝓝[>] 0) (𝓝 (derivWithin f (Ioi 0) 0)) := by
    simpa only [slope_fun_def_field, sub_zero, zero_smul, add_zero] using hl
  have he : dirDeriv g x d = derivWithin f (Ioi 0) 0 := by
    exact hl'.limUnder_eq
  rwa [he]


open MeasureTheory ProbabilityTheory Filter Topology

theorem SAARate.Sharp.display_2_10 {m : ℕ} {Ω : Type*} (h : E m → Ω → ℝ)
    (hconv : ∀ ω, ConvexOn ℝ Set.univ (fun x => h x ω))
    (s : ℕ → Ω) (N : ℕ) (hN : 1 ≤ N) (x d : E m) :
    dirDeriv (saaObj h s N) x d =
      (N : ℝ)⁻¹ * ∑ j ∈ Finset.range N, dirDeriv (fun y => h y (s j)) x d := by
  have hl : Tendsto (fun t : ℝ => (saaObj h s N (x + t • d) - saaObj h s N x) / t)
      (𝓝[>] 0) (𝓝 ((N : ℝ)⁻¹ * ∑ j ∈ Finset.range N, dirDeriv (fun y => h y (s j)) x d)) := by
    have hs := tendsto_finsetSum (Finset.range N)
      (fun j _ => quotient_tendsto (fun y => h y (s j)) (hconv (s j)) x d)
    convert tendsto_const_nhds.mul hs using 1
    funext t
    simp only [saaObj]
    rw [← Finset.sum_div, Finset.sum_sub_distrib]
    ring
  exact hl.limUnder_eq


theorem solution {m : ℕ} {Ω : Type*} (h : E m → Ω → ℝ)
    (hconv : ∀ ω, ConvexOn ℝ Set.univ (fun x => h x ω))
    (s : ℕ → Ω) (N : ℕ) (hN : 1 ≤ N) (x d : E m) :
    dirDeriv (saaObj h s N) x d =
      (N : ℝ)⁻¹ * ∑ j ∈ Finset.range N, dirDeriv (fun y => h y (s j)) x d  := by
  exact SAARate.Sharp.display_2_10 h hconv s N hN x d

#print axioms solution
