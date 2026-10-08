-- Prove2me | solution 1 for WeightedRootIntegralIdentity.weightedRootApplyAcceptedLimitLemmas
-- status  : ACCEPTED   (prove)
-- author  : @abcdefg
-- created : 2026-09-20T05:08:06.480776+00:00
-- url     : https://prove2.me/submissions/e8c6b541-7ecb-4067-a6ad-20f7d3b983e8

import Mathlib
open Filter Topology

theorem solution
    (Iu Il Vr Vl Ii Io : ℕ → ℂ) (U L residue : ℂ)
    (hu : Tendsto Iu atTop (𝓝 U))
    (hl : Tendsto Il atTop (𝓝 L))
    (hvr : Tendsto Vr atTop (𝓝 0))
    (hvl : Tendsto Vl atTop (𝓝 0))
    (hi : Tendsto Ii atTop (𝓝 0))
    (ho : Tendsto Io atTop (𝓝 0))
    (hfinite : ∀ m : ℕ,
      Iu m + Il m + Vr m + Vl m + Ii m + Io m = residue) :
    U + L = residue := by
  have hsum : Tendsto (fun m : ℕ =>
      Iu m + Il m + Vr m + Vl m + Ii m + Io m)
      atTop (𝓝 (U + L)) := by
    simpa using (((((hu.add hl).add hvr).add hvl).add hi).add ho)
  have hconst : Tendsto (fun _ : ℕ => residue) atTop (𝓝 residue) :=
    tendsto_const_nhds
  have hfun : (fun m : ℕ =>
      Iu m + Il m + Vr m + Vl m + Ii m + Io m) =
      (fun _ : ℕ => residue) := by
    funext m
    exact hfinite m
  rw [hfun] at hsum
  exact tendsto_nhds_unique hsum hconst
