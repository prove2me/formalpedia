-- Prove2me | solution 1 for SoficGroups.SourceCommonOffsetMidrankEnergy.exists_common_component_log_rank_with_vanishing_midrank_energy
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:00.855273+00:00
-- url     : https://prove2.me/submissions/90f13bfc-68bf-4cfd-83b8-69310963dce3

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_MidrankPermutationEnergy_partitionVertexMidrank_permutation_energy_tendsto_zero
import Theorems.Thm_SoficGroups_SourceCommonOffsetMidrankEnergy_exists_common_component_log_rank_with_vanishing_drops

set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.SourceCommonOffsetMidrankEnergy
open Filter Topology
open scoped BigOperators
namespace SoficGroups.SourceCommonOffsetMidrankEnergy
theorem _root_.solution
    (V : ℕ → Type*)
    [∀ n, Fintype (V n)] [∀ n, Nonempty (V n)]
    [∀ n, DecidableEq (V n)]
    (ι : Type*) [Fintype ι]
    (Q A : (n : ℕ) → Finpartition (Finset.univ : Finset (V n)))
    (p : (n : ℕ) → ι → Equiv.Perm (V n))
    (eta H : ℕ → ℝ)
    (heta0 : ∀ n, 0 ≤ eta n)
    (heta1 : ∀ n, eta n < 1)
    (hH : ∀ n, 0 < H n)
    (heta : Tendsto eta atTop (nhds 0))
    (hratio : Tendsto (fun n => eta n / H n) atTop (nhds 0))
    (hbad : Tendsto
      (fun n =>
        ((componentSizeComparisonBad (Q n) (p n) (eta n)).card : ℝ) /
          Fintype.card (V n))
      atTop (nhds 0))
    (hcross : Tendsto
      (fun n =>
        (∑ i : ι,
          ((SoficGroups.partitionWordCrossing (A n) (p n i)).card : ℝ)) /
            Fintype.card (V n))
      atTop (nhds 0)) :
    ∃ r : ℕ → ℝ,
      (∀ n, r n ∈ Set.Ico 0 (H n)) ∧
      Tendsto
        (fun n =>
          (∑ i : ι,
            ((SoficGroups.MidrankPermutationEnergy.rankDecreasingVertices
              Finset.univ
              (componentLogRank (Q n) (H n) (r n))
              (p n i)).card : ℝ)) /
            Fintype.card (V n))
        atTop (nhds 0) ∧
      Tendsto
        (fun n =>
          (∑ i : ι, ∑ x : V n,
            (SoficGroups.MidrankPermutationEnergy.partitionVertexMidrank
              (A n) (componentLogRank (Q n) (H n) (r n)) (p n i x) -
             SoficGroups.MidrankPermutationEnergy.partitionVertexMidrank
              (A n) (componentLogRank (Q n) (H n) (r n)) x) ^ 2) /
            Fintype.card (V n))
        atTop (nhds 0) := by
  obtain ⟨r, hr, hdrop⟩ :=
    exists_common_component_log_rank_with_vanishing_drops
      V ι Q p eta H heta0 heta1 hH heta hratio hbad
  refine ⟨r, hr, hdrop, ?_⟩
  apply SoficGroups.MidrankPermutationEnergy.partitionVertexMidrank_permutation_energy_tendsto_zero
      V (fun _ => ι) A
      (fun n => componentLogRank (Q n) (H n) (r n)) p
      (fun n => (Fintype.card (V n) : ℝ))
  · intro n
    exact_mod_cast Fintype.card_pos_iff.mpr inferInstance
  · exact hcross
  · exact hdrop
end SoficGroups.SourceCommonOffsetMidrankEnergy
