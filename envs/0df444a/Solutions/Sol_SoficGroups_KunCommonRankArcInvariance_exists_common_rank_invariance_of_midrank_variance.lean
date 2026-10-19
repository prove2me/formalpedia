-- Prove2me | solution 1 for SoficGroups.KunCommonRankArcInvariance.exists_common_rank_invariance_of_midrank_variance
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:00.855273+00:00
-- url     : https://prove2.me/submissions/2abf3632-bcfe-46fc-9f5c-363191309677

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_KunCommonRankArcInvariance_exists_maximizing_partition_ranks
import Theorems.Thm_SoficGroups_KunCommonRankArcInvariance_maximizing_partition_rank_omitted_density_tendsto_zero
import Theorems.Thm_SoficGroups_KunCommonRankArcInvariance_rankChangingArc_density_tendsto_zero_of_selected_support

set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.KunCommonRankArcInvariance
open Filter Topology
open scoped BigOperators
namespace SoficGroups.KunCommonRankArcInvariance
theorem _root_.solution
    {V : ℕ → Type*}
    [∀ n, Fintype (V n)] [∀ n, Nonempty (V n)]
    [∀ n, DecidableEq (V n)]
    {κ : Type*}
    (P : (n : ℕ) → Finpartition (Finset.univ : Finset (V n)))
    (b : (n : ℕ) → V n → ℤ)
    (w : (n : ℕ) → κ → Equiv.Perm (V n))
    (hvariance : Tendsto
      (fun n =>
        (∑ C ∈ (P n).parts,
          (C.card : ℝ) *
            SoficGroups.midrankVariance
              (SoficGroups.componentRankMassList C (b n))) /
                Fintype.card (V n))
      atTop (nhds 0))
    (hcross : ∀ i : κ, Tendsto
      (fun n =>
        ((SoficGroups.partitionWordCrossing
          (P n) (w n i)).card : ℝ) /
            Fintype.card (V n))
      atTop (nhds 0)) :
    ∃ j : (n : ℕ) → Finset (V n) → ℤ,
      (∀ n C, C ∈ (P n).parts →
        j n C ∈ C.image (b n) ∧
          ∀ k ∈ C.image (b n),
            SoficGroups.componentRankMass C (b n) k ≤
              SoficGroups.componentRankMass C (b n) (j n C)) ∧
      Tendsto
        (fun n =>
          ((((Finset.univ : Finset (V n)) \
            SoficGroups.RankArcCharging.selectedRankSupport
              (P n) (b n) (j n)).card : ℝ) /
                Fintype.card (V n)))
        atTop (nhds 0) ∧
      ∀ i : κ, Tendsto
        (fun n =>
          ((SoficGroups.RankArcCharging.rankChangingArc
            (Finset.univ : Finset (V n))
            (b n) (w n i)).card : ℝ) /
              Fintype.card (V n))
        atTop (nhds 0) := by
  obtain ⟨j, hj⟩ := exists_maximizing_partition_ranks P b
  have homitted :=
    maximizing_partition_rank_omitted_density_tendsto_zero
      P b j (fun n C hC => (hj n C hC).2) hvariance
  exact ⟨j, hj, homitted,
    rankChangingArc_density_tendsto_zero_of_selected_support
      P b j w homitted hcross⟩
end SoficGroups.KunCommonRankArcInvariance
