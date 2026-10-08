-- Prove2me | solution 1 for WeightedRootIntegralIdentity.concrete_finite_to_limiting_residue_balance
-- status  : ACCEPTED   (prove)
-- author  : @abcdefg
-- created : 2026-09-16T14:47:39.370409+00:00
-- url     : https://prove2.me/submissions/6fa8b84a-54f8-41ea-a95a-c195f42ff814

import Mathlib

open Filter Topology

theorem solution
    (Iu Il Ii Io : ℕ → ℂ) (U L A B residue : ℂ)
    (hu : Tendsto Iu atTop (𝓝 U))
    (hl : Tendsto Il atTop (𝓝 L))
    (hi : Tendsto Ii atTop (𝓝 A))
    (ho : Tendsto Io atTop (𝓝 B))
    (hfinite : ∀ m : ℕ,
      Iu m + Il m + Ii m + Io m = 2 * Real.pi * Complex.I * residue) :
    U + L + A + B = 2 * Real.pi * Complex.I * residue := by
  have hsum : Tendsto (fun m : ℕ => Iu m + Il m + Ii m + Io m)
      atTop (𝓝 (U + L + A + B)) := by
    exact (((hu.add hl).add hi).add ho)
  have hconst : Tendsto (fun _ : ℕ => 2 * Real.pi * Complex.I * residue)
      atTop (𝓝 (2 * Real.pi * Complex.I * residue)) := tendsto_const_nhds
  have hfun : (fun m : ℕ => Iu m + Il m + Ii m + Io m) =
      (fun _ : ℕ => 2 * Real.pi * Complex.I * residue) := by
    funext m
    exact hfinite m
  rw [hfun] at hsum
  exact tendsto_nhds_unique hsum hconst
