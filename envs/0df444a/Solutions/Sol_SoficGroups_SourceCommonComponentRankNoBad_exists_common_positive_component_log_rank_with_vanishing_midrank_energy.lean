-- Prove2me | solution 1 for SoficGroups.SourceCommonComponentRankNoBad.exists_common_positive_component_log_rank_with_vanishing_midrank_energy
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:00.855273+00:00
-- url     : https://prove2.me/submissions/ad27d7e9-7b2b-48f8-a622-33db25b24b0d

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_SourceCommonComponentComparisonBad_combined_positive_comparisonBad_density_tendsto_zero
import Theorems.Thm_SoficGroups_SourceCommonOffsetMidrankEnergy_exists_common_component_log_rank_with_vanishing_midrank_energy

set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.SourceCommonComponentRankNoBad
open Filter Topology
open scoped BigOperators
namespace SoficGroups.SourceCommonComponentRankNoBad
theorem _root_.solution
    (V : ℕ → Type*)
    [∀ n, Fintype (V n)] [∀ n, Nonempty (V n)]
    [∀ n, DecidableEq (V n)]
    (ι κ : Type*) [Fintype ι] [Fintype κ]
    (Q A : (n : ℕ) → Finpartition (Finset.univ : Finset (V n)))
    (σ : (n : ℕ) → ι → Equiv.Perm (V n))
    (T : (n : ℕ) → κ → Equiv.Perm (V n))
    (eta H : ℕ → ℝ)
    (heta0 : ∀ n, 0 ≤ eta n)
    (heta1 : ∀ n, eta n < 1)
    (hH : ∀ n, 0 < H n)
    (heta : Tendsto eta atTop (nhds 0))
    (hratio : Tendsto (fun n => eta n / H n) atTop (nhds 0))
    (hcrossQ : ∀ i : ι, Tendsto
      (fun n =>
        ((SoficGroups.partitionWordCrossing
          (Q n) (σ n i)).card : ℝ) /
            Fintype.card (V n))
      atTop (nhds 0))
    (hoverlap : ∀ j : κ, Tendsto
      (fun n =>
        (∑ C ∈ SoficGroups.insufficientOverlapComponents
          (SoficGroups.transportedUnivFinpartition
            (Q n) (T n j)) (Q n) (eta n), (C.card : ℝ)) /
              Fintype.card (V n))
      atTop (nhds 0))
    (hloss : ∀ j : κ, Tendsto
      (fun n =>
        (∑ C ∈
          (SoficGroups.transportedUnivFinpartition
            (Q n) (T n j)).parts,
          ((C.card : ℝ) -
            ((C ∩ SoficGroups.maximumOverlapPart (Q n) C).card : ℝ))) /
              Fintype.card (V n))
      atTop (nhds 0))
    (hcrossA : Tendsto
      (fun n =>
        (∑ i : ι ⊕ κ,
          ((SoficGroups.partitionWordCrossing
            (A n) (Sum.elim (σ n) (T n) i)).card : ℝ)) /
              Fintype.card (V n))
      atTop (nhds 0)) :
    ∃ r : ℕ → ℝ,
      (∀ n, r n ∈ Set.Ico 0 (H n)) ∧
      Tendsto
        (fun n =>
          (∑ i : ι ⊕ κ,
            ((SoficGroups.MidrankPermutationEnergy.rankDecreasingVertices
              Finset.univ
              (SoficGroups.SourceCommonOffsetMidrankEnergy.componentLogRank
                (Q n) (H n) (r n))
              (Sum.elim (σ n) (T n) i)).card : ℝ)) /
            Fintype.card (V n))
        atTop (nhds 0) ∧
      Tendsto
        (fun n =>
          (∑ i : ι ⊕ κ, ∑ x : V n,
            (SoficGroups.MidrankPermutationEnergy.partitionVertexMidrank
              (A n)
              (SoficGroups.SourceCommonOffsetMidrankEnergy.componentLogRank
                (Q n) (H n) (r n))
              (Sum.elim (σ n) (T n) i x) -
             SoficGroups.MidrankPermutationEnergy.partitionVertexMidrank
              (A n)
              (SoficGroups.SourceCommonOffsetMidrankEnergy.componentLogRank
                (Q n) (H n) (r n)) x) ^ 2) /
            Fintype.card (V n))
        atTop (nhds 0) := by
  have hsource :=
    SoficGroups.SourceCommonComponentComparisonBad.combined_positive_comparisonBad_density_tendsto_zero
        V ι κ Q σ T eta heta0 hcrossQ hoverlap hloss
  have hsets (n : ℕ) :
      SoficGroups.SourceCommonOffsetMidrankEnergy.componentSizeComparisonBad
        (Q n) (Sum.elim (σ n) (T n)) (eta n) =
      SoficGroups.SourceCommonComponentComparisonBad.familyComparisonBad
        (Q n) (Sum.elim (σ n) (T n)) (eta n) := by
    classical
    ext e
    constructor
    · intro he
      unfold
        SoficGroups.SourceCommonOffsetMidrankEnergy.componentSizeComparisonBad
        at he
      have hfail := (Finset.mem_filter.mp he).2
      unfold SoficGroups.SourceCommonComponentComparisonBad.familyComparisonBad
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      simpa only
        [SoficGroups.SourceCommonOffsetMidrankEnergy.realComponentSize]
        using hfail
    · intro he
      unfold
        SoficGroups.SourceCommonComponentComparisonBad.familyComparisonBad
        at he
      have hfail := (Finset.mem_filter.mp he).2
      unfold
        SoficGroups.SourceCommonOffsetMidrankEnergy.componentSizeComparisonBad
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      simpa only
        [SoficGroups.SourceCommonOffsetMidrankEnergy.realComponentSize]
        using hfail
  have hbad : Tendsto
      (fun n =>
        ((SoficGroups.SourceCommonOffsetMidrankEnergy.componentSizeComparisonBad
          (Q n) (Sum.elim (σ n) (T n)) (eta n)).card : ℝ) /
            Fintype.card (V n))
      atTop (nhds 0) := by
    simpa only [hsets] using hsource
  exact
    SoficGroups.SourceCommonOffsetMidrankEnergy.exists_common_component_log_rank_with_vanishing_midrank_energy
        V (ι ⊕ κ) Q A (fun n => Sum.elim (σ n) (T n))
        eta H heta0 heta1 hH heta hratio hbad hcrossA
end SoficGroups.SourceCommonComponentRankNoBad
