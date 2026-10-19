-- Prove2me | solution 1 for SoficGroups.KunTransportedAmbientOverlap.transported_partition_boundary_density_tendsto_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:00.272868+00:00
-- url     : https://prove2.me/submissions/e3549b98-5ff1-4887-b13f-b905a704b9df

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_KunTransportedAmbientOverlap_sum_boundary_transportedUnivFinpartition

set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.KunTransportedAmbientOverlap
open Filter Topology
open scoped BigOperators symmDiff
namespace SoficGroups.KunTransportedAmbientOverlap
theorem _root_.solution
    {V : ℕ → Type*}
    [∀ n, Fintype (V n)] [∀ n, DecidableEq (V n)]
    {ι : Type*} [Fintype ι]
    (Q : ∀ n, Finpartition (Finset.univ : Finset (V n)))
    (σ : (n : ℕ) → ι → Equiv.Perm (V n))
    (T : (n : ℕ) → Equiv.Perm (V n))
    (hboundary : Tendsto
      (fun n =>
        (∑ C ∈ (Q n).parts,
          (SoficGroups.boundary (σ n) C : ℝ)) /
            Fintype.card (V n))
      atTop (nhds 0)) :
    Tendsto
      (fun n =>
        (∑ C ∈
          (SoficGroups.transportedUnivFinpartition (Q n) (T n)).parts,
            (SoficGroups.boundary
              (fun i => T n * σ n i * (T n)⁻¹) C : ℝ)) /
                Fintype.card (V n))
      atTop (nhds 0) := by
  have hsum (n : ℕ) :
      (∑ C ∈
        (SoficGroups.transportedUnivFinpartition (Q n) (T n)).parts,
          (SoficGroups.boundary
            (fun i => T n * σ n i * (T n)⁻¹) C : ℝ)) =
        ∑ C ∈ (Q n).parts,
          (SoficGroups.boundary (σ n) C : ℝ) := by
    exact_mod_cast
      sum_boundary_transportedUnivFinpartition (Q n) (σ n) (T n)
  simpa only [hsum] using hboundary
end SoficGroups.KunTransportedAmbientOverlap
