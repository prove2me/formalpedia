-- Prove2me | solution 1 for WeightedRootIntegralIdentity.weightedRootConcreteResidueCauchyBalanceV3
-- status  : ACCEPTED   (prove)
-- author  : @abcdefg
-- created : 2026-09-20T06:08:44.55074+00:00
-- url     : https://prove2.me/submissions/46a4419d-476e-4614-9bb2-8b00864c7790

import Mathlib
open Filter Topology
open scoped BigOperators Interval

theorem solution
    (n : ℕ) (a w : ℕ → ℝ) (Iu Il Vr Vl Ii Io : ℕ → ℂ) (U L : ℂ)
    (hu : Tendsto Iu atTop (𝓝 U))
    (hl : Tendsto Il atTop (𝓝 L))
    (hvr : Tendsto Vr atTop (𝓝 0))
    (hvl : Tendsto Vl atTop (𝓝 0))
    (hi : Tendsto Ii atTop (𝓝 0))
    (ho : Tendsto Io atTop (𝓝 0))
    (hfinite : ∀ m : ℕ,
      Iu m + Il m + Vr m + Vl m + Ii m + Io m =
        2 * Real.pi * Complex.I *
          (-(deriv (fun u : ℂ =>
            ∏ i ∈ Finset.range n, (1 - (a i : ℂ) * u) ^ (w i : ℂ)) 0).re +
            (∏ i ∈ Finset.range n,
              (((0 : ℂ) - (a i : ℂ)) ^ (w i : ℂ))).re)) :
    U + L = 2 * Real.pi * Complex.I *
      (-(deriv (fun u : ℂ =>
        ∏ i ∈ Finset.range n, (1 - (a i : ℂ) * u) ^ (w i : ℂ)) 0).re +
        (∏ i ∈ Finset.range n,
          (((0 : ℂ) - (a i : ℂ)) ^ (w i : ℂ))).re) := by
  let ρ : ℂ := 2 * Real.pi * Complex.I *
      (-(deriv (fun u : ℂ =>
        ∏ i ∈ Finset.range n, (1 - (a i : ℂ) * u) ^ (w i : ℂ)) 0).re +
        (∏ i ∈ Finset.range n,
          (((0 : ℂ) - (a i : ℂ)) ^ (w i : ℂ))).re)
  have hsum : Tendsto (fun m : ℕ =>
      Iu m + Il m + Vr m + Vl m + Ii m + Io m)
      atTop (𝓝 (U + L)) := by
    simpa using (((((hu.add hl).add hvr).add hvl).add hi).add ho)
  have hconst : Tendsto (fun _ : ℕ => ρ) atTop (𝓝 ρ) := tendsto_const_nhds
  have hfun : (fun m : ℕ => Iu m + Il m + Vr m + Vl m + Ii m + Io m) =
      (fun _ : ℕ => ρ) := by
    funext m
    simpa [ρ] using hfinite m
  rw [hfun] at hsum
  have heq : U + L = ρ := tendsto_nhds_unique hsum hconst
  simpa [ρ] using heq
