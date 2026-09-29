-- Prove2me | solution 1 for Rudin.ch08_bessel_identity
-- status  : ACCEPTED   (prove)
-- author  : @Lucas
-- created : 2026-09-18T14:32:57.851142+00:00
-- url     : https://prove2.me/submissions/98e63b19-5003-4ed4-a08d-da299da28be7

import Mathlib
import Definitions.Def_Rudin_ch08_fourier

open Filter Topology
open MeasureTheory

namespace RudinBesselAux

/-- The sesquilinear pairing `⟪u, v⟫ = ∫ u * conj v` for a measure `μ` on `ℝ`. -/
noncomputable def pair (μ : Measure ℝ) (u v : ℝ → ℂ) : ℂ :=
  ∫ x, u x * (starRingEnd ℂ) (v x) ∂μ

variable {μ : Measure ℝ}

lemma memLp_star {v : ℝ → ℂ} (hv : MemLp v 2 μ) :
    MemLp (fun x => (starRingEnd ℂ) (v x)) 2 μ := by
  simpa [Pi.star_def, Complex.star_def] using hv.star

lemma integrable_mul_conj {u v : ℝ → ℂ} (hu : MemLp u 2 μ) (hv : MemLp v 2 μ) :
    Integrable (fun x => u x * (starRingEnd ℂ) (v x)) μ := by
  have := hu.integrable_mul (memLp_star hv)
  simpa [Pi.mul_def] using this

lemma pair_self_ofReal (u : ℝ → ℂ) :
    pair μ u u = ((∫ x, ‖u x‖ ^ 2 ∂μ : ℝ) : ℂ) := by
  have h : (fun x => u x * (starRingEnd ℂ) (u x)) = fun x => ((‖u x‖ ^ 2 : ℝ) : ℂ) := by
    funext x
    rw [Complex.mul_conj']
    push_cast
    ring
  rw [pair, h, integral_complex_ofReal]

lemma pair_symm (u v : ℝ → ℂ) : pair μ v u = (starRingEnd ℂ) (pair μ u v) := by
  rw [pair, pair, ← integral_conj]
  simp [mul_comm]

lemma pair_sub_left {u v w : ℝ → ℂ} (hu : MemLp u 2 μ) (hv : MemLp v 2 μ) (hw : MemLp w 2 μ) :
    pair μ (fun x => u x - v x) w = pair μ u w - pair μ v w := by
  have h1 := integrable_mul_conj hu hw
  have h2 := integrable_mul_conj hv hw
  simp only [pair, sub_mul]
  exact integral_sub h1 h2

lemma pair_sub_right {u v w : ℝ → ℂ} (hu : MemLp u 2 μ) (hv : MemLp v 2 μ) (hw : MemLp w 2 μ) :
    pair μ u (fun x => v x - w x) = pair μ u v - pair μ u w := by
  have h1 := integrable_mul_conj hu hv
  have h2 := integrable_mul_conj hu hw
  simp only [pair, map_sub, mul_sub]
  exact integral_sub h1 h2

lemma memLp_linear_combination {ψ : ℕ → ℝ → ℂ} (hψ : ∀ m, MemLp (ψ m) 2 μ) (s : Finset ℕ)
    (γ : ℕ → ℂ) : MemLp (fun x => ∑ m ∈ s, γ m * ψ m x) 2 μ := by
  have h : (fun x => ∑ m ∈ s, γ m * ψ m x) = ∑ m ∈ s, fun x => γ m * ψ m x := by
    funext x
    simp [Finset.sum_apply]
  rw [h]
  exact memLp_finsetSum' (μ := μ) (p := 2) s (fun m _ => (hψ m).const_mul (γ m))

lemma pair_combination_right {u : ℝ → ℂ} (hu : MemLp u 2 μ) {ψ : ℕ → ℝ → ℂ}
    (hψ : ∀ m, MemLp (ψ m) 2 μ) (s : Finset ℕ) (γ : ℕ → ℂ) :
    pair μ u (fun x => ∑ m ∈ s, γ m * ψ m x) =
      ∑ m ∈ s, (starRingEnd ℂ) (γ m) * pair μ u (ψ m) := by
  have h : (fun x => u x * (starRingEnd ℂ) (∑ m ∈ s, γ m * ψ m x)) =
      fun x => ∑ m ∈ s, (starRingEnd ℂ) (γ m) * (u x * (starRingEnd ℂ) (ψ m x)) := by
    funext x
    rw [map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [map_mul]
    ring
  rw [pair, h, integral_finsetSum]
  · simp only [pair]
    exact Finset.sum_congr rfl fun m _ => by
      rw [integral_const_mul]
  · exact fun m _ => ((integrable_mul_conj hu (hψ m)).const_mul _)

lemma pair_combination_left {w : ℝ → ℂ} (hw : MemLp w 2 μ) {ψ : ℕ → ℝ → ℂ}
    (hψ : ∀ m, MemLp (ψ m) 2 μ) (s : Finset ℕ) (γ : ℕ → ℂ) :
    pair μ (fun x => ∑ m ∈ s, γ m * ψ m x) w = ∑ m ∈ s, γ m * pair μ (ψ m) w := by
  have h : (fun x => (∑ m ∈ s, γ m * ψ m x) * (starRingEnd ℂ) (w x)) =
      fun x => ∑ m ∈ s, γ m * (ψ m x * (starRingEnd ℂ) (w x)) := by
    funext x
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun m _ => by ring
  rw [pair, h, integral_finsetSum]
  · simp only [pair]
    exact Finset.sum_congr rfl fun m _ => by rw [integral_const_mul]
  · exact fun m _ => ((integrable_mul_conj (hψ m) hw).const_mul _)

end RudinBesselAux

open RudinBesselAux Rudin

/-- Rudin, Theorems 8.11 and 8.12, in the exact form of the identity behind them. -/
theorem solution (a b : ℝ) (hab : a ≤ b) (φ : ℕ → ℝ → ℂ)
    (hφ : IsOrthonormalSystem φ a b)
    (hφint : ∀ m, IntervalIntegrable (φ m) MeasureTheory.volume a b)
    (f : ℝ → ℂ) (hf : IntervalIntegrable f MeasureTheory.volume a b)
    (hf2 : IntervalIntegrable (fun x => ‖f x‖ ^ 2) MeasureTheory.volume a b)
    (n : ℕ) (γ : ℕ → ℂ) :
    (∫ x in a..b, ‖f x - ∑ m ∈ Finset.range n, γ m * φ m x‖ ^ 2) =
      (∫ x in a..b, ‖f x‖ ^ 2) - (∑ m ∈ Finset.range n, ‖genFourierCoeff f φ a b m‖ ^ 2)
        + ∑ m ∈ Finset.range n, ‖γ m - genFourierCoeff f φ a b m‖ ^ 2 := by
  classical
  set μ : Measure ℝ := MeasureTheory.volume.restrict (Set.Ioc a b) with hμdef
  -- membership in `L²`
  have hFmem : MemLp f 2 μ :=
    (memLp_two_iff_integrable_sq_norm hf.1.aestronglyMeasurable).2 hf2.1
  have hφsq : ∀ m, Integrable (fun x => ‖φ m x‖ ^ 2) μ := by
    intro m
    by_contra hcon
    have h1 := hφ.2 m
    rw [intervalIntegral.integral_of_le hab, integral_undef hcon] at h1
    norm_num at h1
  have hΦmem : ∀ m, MemLp (φ m) 2 μ := fun m =>
    (memLp_two_iff_integrable_sq_norm (hφint m).1.aestronglyMeasurable).2 (hφsq m)
  set S : ℝ → ℂ := fun x => ∑ m ∈ Finset.range n, γ m * φ m x with hSdef
  have hSmem : MemLp S 2 μ := memLp_linear_combination hΦmem _ γ
  have hDmem : MemLp (fun x => f x - S x) 2 μ := by
    simpa [Pi.sub_def] using hFmem.sub hSmem
  set c : ℕ → ℂ := fun m => genFourierCoeff f φ a b m with hcdef
  have hc : ∀ m, c m = pair μ f (φ m) := by
    intro m
    simp only [hcdef, genFourierCoeff, pair]
    exact intervalIntegral.integral_of_le hab
  -- orthonormality, expressed through the pairing
  have hpair_ne : ∀ i j, i ≠ j → pair μ (φ i) (φ j) = 0 := by
    intro i j hij
    have h1 := hφ.1 j i (Ne.symm hij)
    rw [intervalIntegral.integral_of_le hab] at h1
    exact h1
  have hpair_self : ∀ m, pair μ (φ m) (φ m) = 1 := by
    intro m
    rw [pair_self_ofReal]
    have h1 := hφ.2 m
    rw [intervalIntegral.integral_of_le hab] at h1
    rw [h1]
    norm_num
  -- the three pairings involving the linear combination `S`
  have hfS : pair μ f S = ∑ m ∈ Finset.range n, (starRingEnd ℂ) (γ m) * c m := by
    rw [hSdef, pair_combination_right hFmem hΦmem]
    exact Finset.sum_congr rfl fun m _ => by rw [hc m]
  have hSf : pair μ S f = ∑ m ∈ Finset.range n, γ m * (starRingEnd ℂ) (c m) := by
    rw [hSdef, pair_combination_left hFmem hΦmem]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [pair_symm, hc m]
  have hSS : pair μ S S = ∑ m ∈ Finset.range n, γ m * (starRingEnd ℂ) (γ m) := by
    nth_rewrite 1 [hSdef]
    rw [pair_combination_left hSmem hΦmem]
    refine Finset.sum_congr rfl fun m hm => ?_
    have : pair μ (φ m) S = (starRingEnd ℂ) (γ m) := by
      rw [hSdef, pair_combination_right (hΦmem m) hΦmem]
      rw [Finset.sum_eq_single m]
      · rw [hpair_self m, mul_one]
      · intro k _ hkm
        rw [hpair_ne m k (Ne.symm hkm), mul_zero]
      · intro hnm
        exact absurd hm hnm
    rw [this]
  -- the identity, as an identity between complex numbers
  have main : ((∫ x in a..b, ‖f x - S x‖ ^ 2 : ℝ) : ℂ)
      = ((∫ x in a..b, ‖f x‖ ^ 2 : ℝ) : ℂ)
        - ∑ m ∈ Finset.range n, ((‖c m‖ ^ 2 : ℝ) : ℂ)
        + ∑ m ∈ Finset.range n, ((‖γ m - c m‖ ^ 2 : ℝ) : ℂ) := by
    have hL : ((∫ x in a..b, ‖f x - S x‖ ^ 2 : ℝ) : ℂ)
        = pair μ (fun x => f x - S x) (fun x => f x - S x) := by
      rw [pair_self_ofReal, intervalIntegral.integral_of_le hab]
    have hR : ((∫ x in a..b, ‖f x‖ ^ 2 : ℝ) : ℂ) = pair μ f f := by
      rw [pair_self_ofReal, intervalIntegral.integral_of_le hab]
    have hsplit : pair μ (fun x => f x - S x) (fun x => f x - S x)
        = (pair μ f f - pair μ f S) - (pair μ S f - pair μ S S) := by
      rw [pair_sub_left hFmem hSmem hDmem, pair_sub_right hFmem hFmem hSmem,
        pair_sub_right hSmem hFmem hSmem]
    have hnorm : ∀ z : ℂ, ((‖z‖ ^ 2 : ℝ) : ℂ) = z * (starRingEnd ℂ) z := by
      intro z
      rw [Complex.mul_conj']
      push_cast
      ring
    have hexp : ∑ m ∈ Finset.range n, ((‖γ m - c m‖ ^ 2 : ℝ) : ℂ)
        = ∑ m ∈ Finset.range n, (γ m * (starRingEnd ℂ) (γ m)
            - (starRingEnd ℂ) (γ m) * c m - γ m * (starRingEnd ℂ) (c m)
            + c m * (starRingEnd ℂ) (c m)) := by
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [hnorm]
      rw [map_sub]
      ring
    rw [hL, hsplit, hR, hfS, hSf, hSS, hexp]
    simp only [hnorm, Finset.sum_add_distrib, Finset.sum_sub_distrib]
    ring
  exact_mod_cast main

