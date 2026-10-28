-- Prove2me | solution 1 for ZeroFreeBridge.dense_inter_sphere_of_codiscrete
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-28T07:43:44.241814+00:00
-- url     : https://prove2.me/submissions/ba246930-2983-4acf-8091-53e5a88a3bd8

import Mathlib

/- PHASE 4 (dVP frontier, BLASCHKE step 1 — DENSITY DISCHARGE): a codiscrete subset of the closed
   ball is dense within the boundary sphere.

   `DlvpBlaschkeSphere.norm_eq_of_codiscrete_factor_on_sphere` isolated one hypothesis: the
   agreement set of the codiscrete factorization is DENSE in `sphere 0 R`.  This file discharges it.

   The sphere is CONNECTED (`isConnected_sphere`, since `ℂ` has real rank 2) and nontrivial
   (`R > 0`), hence PREPERFECT (`IsPreconnected.preperfect_of_nontrivial`): every sphere point is an
   accumulation point of the sphere.  A codiscrete set `A` on `closedBall` satisfies `A ∪ (closedBall)ᶜ
   ∈ 𝓝[≠] z`; restricted to the punctured sphere (⊆ `closedBall`), this means `A` holds on the
   accumulating punctured-sphere filter — so every sphere point is a cluster point of `A ∩ sphere`,
   i.e. `sphere ⊆ closure (A ∩ sphere)`.  Function-agnostic.  conjecture1_proved = False (NOT RH).
-/


open Complex Metric Filter Topology Set

section
namespace ZeroFreeBridge
end ZeroFreeBridge
open ZeroFreeBridge


theorem solution {A : Set ℂ} {R : ℝ} (hR : 0 < R)
    (hA : A ∈ codiscreteWithin (closedBall (0 : ℂ) R)) :
    sphere (0 : ℂ) R ⊆ closure (A ∩ sphere 0 R) := by
  -- the sphere is preperfect (connected + nontrivial).
  have hrank : 1 < Module.rank ℝ ℂ := by rw [Complex.rank_real_complex]; norm_num
  have hconn : IsPreconnected (sphere (0 : ℂ) R) :=
    (isConnected_sphere hrank 0 hR.le).isPreconnected
  have hntriv : (sphere (0 : ℂ) R).Nontrivial := by
    refine ⟨(R : ℂ), ?_, (-R : ℂ), ?_, ?_⟩
    · rw [mem_sphere_zero_iff_norm]; simp [Complex.norm_real, abs_of_pos hR]
    · rw [mem_sphere_zero_iff_norm]; simp [abs_of_pos hR]
    · intro h
      have hcast : (R : ℝ) = -R := by exact_mod_cast h
      linarith
  have hpp : Preperfect (sphere (0 : ℂ) R) := hconn.preperfect_of_nontrivial hntriv
  intro z hz
  have hzcb : z ∈ closedBall (0 : ℂ) R := sphere_subset_closedBall hz
  -- the punctured-sphere filter is NeBot (accumulation).
  have hFne : (𝓝[sphere (0 : ℂ) R \ {z}] z).NeBot := accPt_principal_iff_nhdsWithin.mp (hpp z hz)
  -- `A` holds on the punctured-sphere filter.
  have hcodisc : A ∪ (closedBall (0 : ℂ) R)ᶜ ∈ 𝓝[≠] z :=
    (mem_codiscreteWithin_iff_forall_mem_nhdsNE.mp hA) z hzcb
  have hle : 𝓝[sphere (0 : ℂ) R \ {z}] z ≤ 𝓝[≠] z :=
    nhdsWithin_mono z (fun x hx => hx.2)
  have hAmem : A ∈ 𝓝[sphere (0 : ℂ) R \ {z}] z := by
    filter_upwards [hle hcodisc, (self_mem_nhdsWithin :
        (sphere (0 : ℂ) R \ {z}) ∈ 𝓝[sphere (0 : ℂ) R \ {z}] z)] with x hx hxs
    rcases hx with hxA | hxout
    · exact hxA
    · exact absurd (sphere_subset_closedBall hxs.1) hxout
  -- cluster point of `A ∩ sphere`.
  rw [mem_closure_iff_clusterPt]
  have hkey : (𝓝[sphere (0 : ℂ) R \ {z}] z ⊓ 𝓟 A).NeBot := by
    rw [inf_of_le_left (le_principal_iff.mpr hAmem)]; exact hFne
  refine hkey.mono ?_
  have hsub : (sphere (0 : ℂ) R \ {z}) ∩ A ⊆ A ∩ sphere 0 R := fun x hx => ⟨hx.2, hx.1.1⟩
  calc 𝓝[sphere (0 : ℂ) R \ {z}] z ⊓ 𝓟 A
      = 𝓝 z ⊓ (𝓟 (sphere (0 : ℂ) R \ {z}) ⊓ 𝓟 A) := by rw [nhdsWithin, inf_assoc]
    _ = 𝓝 z ⊓ 𝓟 ((sphere (0 : ℂ) R \ {z}) ∩ A) := by rw [inf_principal]
    _ ≤ 𝓝 z ⊓ 𝓟 (A ∩ sphere 0 R) := inf_le_inf_left _ (principal_mono.mpr hsub)
