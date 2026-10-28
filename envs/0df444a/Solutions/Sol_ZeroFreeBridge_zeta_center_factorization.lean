-- Prove2me | solution 1 for ZeroFreeBridge.zeta_center_factorization
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-28T07:53:54.693068+00:00
-- url     : https://prove2.me/submissions/d7d91bfe-a8cb-437e-b923-3c2b1a96ee14

import Mathlib

/- PHASE 4 (dVP frontier, hfac0 — the centre factorization ζ c₀ = B 0 · g 0): the codiscrete→pointwise
   step, the last piece of analysis in item 2.

   The CanonicalDecomp gives `f = B·g` CODISCRETELY (`D.eventuallyEq`), `f = ζ(c₀+·)`.  At the centre `0`
   (where `f 0 = ζ c₀ ≠ 0`, so `0` is not a zero and `B` is analytic), the identity principle upgrades
   this to the POINTWISE `ζ c₀ = B 0 · g 0`: codiscrete membership gives frequent agreement in `𝓝[≠] 0`
   (`mem_codiscreteWithin_iff_forall_mem_nhdsNE`), and both sides continuous at `0` (`f` analytic; `B·g`
   the finite Blaschke product times the analytic `g`) pins the values equal (`tendsto_nhds_unique`,
   `𝓝[≠] 0` NeBot on ℂ).  The continuities are taken as hypotheses (`f` is entire-shifted; `B·g` is
   continuous at `0` since `0` is not among the finitely many zeros).  conjecture1_proved = False.
-/


open Complex MeromorphicOn Metric Filter Topology

section
namespace ZeroFreeBridge
end ZeroFreeBridge
open ZeroFreeBridge


theorem solution {c₀ : ℂ} {R : ℝ} {g : ℂ → ℂ} (hR : 0 < R)
    (D : CanonicalDecomp (fun w => riemannZeta (c₀ + w)) g R)
    (hf_cont0 : ContinuousAt (fun w => riemannZeta (c₀ + w)) 0)
    (hBg_cont0 : ContinuousAt
      ((∏ᶠ u, (canonicalFactor R u) ^ (-divisor (fun w => riemannZeta (c₀ + w)) (ball 0 R) u)) • g) 0) :
    riemannZeta c₀
      = (∏ᶠ u, (canonicalFactor R u) ^ (-divisor (fun w => riemannZeta (c₀ + w)) (ball 0 R) u)) 0
        * g 0 := by
  set B := ∏ᶠ u, (canonicalFactor R u) ^ (-divisor (fun w => riemannZeta (c₀ + w)) (ball 0 R) u) with hB
  -- codiscrete factorization gives frequent agreement in 𝓝[≠] 0
  have h0 : (0 : ℂ) ∈ closedBall (0 : ℂ) R := mem_closedBall_self hR.le
  have hmem : {x | (fun w => riemannZeta (c₀ + w)) x = (B • g) x} ∪ (closedBall (0 : ℂ) R)ᶜ ∈ 𝓝[≠] 0 :=
    (mem_codiscreteWithin_iff_forall_mem_nhdsNE.mp D.eventuallyEq) 0 h0
  have hcb : closedBall (0 : ℂ) R ∈ 𝓝[≠] 0 :=
    mem_nhdsWithin_of_mem_nhds (closedBall_mem_nhds 0 hR)
  have hev : (fun w => riemannZeta (c₀ + w)) =ᶠ[𝓝[≠] 0] (B • g) := by
    filter_upwards [hmem, hcb] with x hx hxcb
    rcases hx with h | h2
    · exact h
    · exact absurd hxcb h2
  -- identity at 0 by continuity + uniqueness of limits
  have hL : Tendsto (fun w => riemannZeta (c₀ + w)) (𝓝[≠] 0) (𝓝 (riemannZeta (c₀ + 0))) :=
    hf_cont0.tendsto.mono_left nhdsWithin_le_nhds
  have hR' : Tendsto (B • g) (𝓝[≠] 0) (𝓝 ((B • g) 0)) :=
    hBg_cont0.tendsto.mono_left nhdsWithin_le_nhds
  have hkey : riemannZeta (c₀ + 0) = (B • g) 0 := tendsto_nhds_unique hL (hR'.congr' hev.symm)
  simpa [Pi.smul_apply', smul_eq_mul] using hkey
