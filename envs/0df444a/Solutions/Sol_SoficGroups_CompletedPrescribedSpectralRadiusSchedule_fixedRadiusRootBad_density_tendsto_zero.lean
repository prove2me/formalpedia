-- Prove2me | solution 1 for SoficGroups.CompletedPrescribedSpectralRadiusSchedule.fixedRadiusRootBad_density_tendsto_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:00.272868+00:00
-- url     : https://prove2.me/submissions/76e0350d-5f63-46c0-b6ac-0718af8bd447

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_finite_union_bad_density_tendsto_zero

set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.CompletedPrescribedSpectralRadiusSchedule
open Filter Topology
open scoped Pointwise
namespace SoficGroups.CompletedPrescribedSpectralRadiusSchedule
theorem _root_.solution
    {G : Type*} [Group G] [DecidableEq G]
    (V : ℕ → Type*)
    [∀ n, Fintype (V n)] [∀ n, DecidableEq (V n)]
    (φ : ∀ n, G → Equiv.Perm (V n))
    (S : Finset G)
    (hmul : ∀ a g : G,
      Tendsto
        (fun n => SoficGroups.normalizedHamming
          (φ n (a * g)) (φ n a * φ n g))
        atTop (𝓝 0))
    (r : ℕ) :
    Tendsto
      (fun n =>
        ((fixedRadiusRootBad (φ n) S r).card : ℝ) /
          Fintype.card (V n))
      atTop (𝓝 0) := by
  classical
  have hpair : ∀ ag ∈ (S ^ r).product (S ^ r),
      Tendsto
        (fun n =>
          (((Finset.univ : Finset (V n)) ∩
            multiplicationBad (φ n) ag.1 ag.2).card : ℝ) /
              (Finset.univ : Finset (V n)).card)
        atTop (𝓝 0) := by
    intro ag _
    simpa [multiplicationBad, SoficGroups.normalizedHamming,
      hammingDist] using hmul ag.1 ag.2
  have h := SoficGroups.finite_union_bad_density_tendsto_zero
    ((S ^ r).product (S ^ r))
    (fun n => (Finset.univ : Finset (V n)))
    (fun n ag => multiplicationBad (φ n) ag.1 ag.2)
    hpair
  simpa [fixedRadiusRootBad] using h
end SoficGroups.CompletedPrescribedSpectralRadiusSchedule
